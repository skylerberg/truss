module Obligation = Obligation
module Lookups = Lookups

module Evaluation_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Obligation.evaluation
end))

type proof =
  | Obligations of Obligation.outcome
  | Unsupported of {
      location : Obligation.location;
      construct : Catalog.Prover.construct;
      foreign : string option;
    }
  | Not_proven_here

let find_inherited_clauses (lookups : Lookups.t) (path : Path.t) =
  Option.bind (Interface.Impls.find_implemented_method lookups.interface path)
    (fun (implemented : Interface.Impls.implemented_method) ->
      Option.map
        (fun clauses -> (clauses, implemented.implementation.substitution))
        (Contracts.find_declared_clauses lookups implemented.declaration))

let translate_impl (lookups : Lookups.t) (key : Resolve.Names.key) source =
  let interface = Interface.Definition.read_impl_interface lookups.interface key.path in
  match Contracts.list_impl_holes lookups key with
  | _ :: _ as holes ->
      if Contracts.has_impl_obligations lookups interface.implements.trait then
        [ { Obligation.obligations = []; holes; evaluated_constants = [] } ]
      else []
  | [] ->
      Translate.translate_laws lookups source ~impl:key.path ~trait:interface.implements
        ~for_type:interface.for_type
        ~proofs:
          (Contracts.list_law_proofs lookups (Path.locate_package key.path) interface.implements
             interface.for_type)
        ~at:Whole_definition
      ::
      (match lookups.interface.names.read_definition key with
      | { kind = Impl { trait_; _ }; _ } ->
          [
            Translate.translate_restated_clauses lookups source ~impl:key.path
              ~trait:interface.implements ~for_type:interface.for_type ~at:(Written trait_.id);
          ]
      | _ -> [])

let list_integer_instances (lookups : Lookups.t) (path : Path.t) =
  let generics =
    match Interface.Impls.read_signature lookups.interface path with
    | Some signature ->
        List.filter_map
          (fun (generic : Types.generic) ->
            match generic.kind with
            | Type_generic bounds ->
                Some (generic.generic, Types.find_bound_integer_implementors bounds)
            | Value_generic -> None)
          signature.generics
    | None -> []
  in
  let self =
    match path with
    | Method { owner; _ } ->
        [ (Types.make_self_parameter owner, Types.find_integer_implementors owner) ]
    | _ -> []
  in
  List.fold_left
    (fun instances ((parameter : Types.parameter), implementors) ->
      match implementors with
      | None -> instances
      | Some builtins ->
          List.concat_map
            (fun (shown, substitution) ->
              List.map
                (fun builtin ->
                  ( shown @ [ (parameter.name, builtin) ],
                    Types.bind_argument parameter
                      (Types.Type (Types.make_builtin builtin))
                      substitution ))
                builtins)
            instances)
    [ ([], Types.no_substitution) ]
    (self @ generics)
  |> List.filter (fun (shown, _) -> shown <> [])

let translate_derived_default (lookups : Lookups.t) (key : Resolve.Names.key)
    (source : State.source) =
  let derives_default =
    match Interface.Definition.find_interface lookups.interface key.path with
    | Some (Interface.Environment.Type_interface interface) ->
        List.exists (Well_known.is Default) interface.derives
    | _ -> Facts.raise_bug "%s is not a type" (Path.show key.path)
  in
  let path =
    Well_known.make_impl_method_path Default_default
      ~impl:(Derived { type_ = key.path; trait = Well_known.make_path Default })
  in
  if derives_default && Option.is_some (Mir.read_code lookups.mir path) then
    let outcome = Translate.translate_function lookups source ~path in
    List.map
      (fun (obligation : Obligation.t) ->
        match Catalog.Prover_description.find_code obligation.obligation with
        | Invariant -> { obligation with obligation = Derived_default_invariant }
        | _ -> obligation)
      outcome.obligations
  else []

let add_defaults lookups source path (outcome : Obligation.outcome) =
  let defaults = Translate.translate_defaults lookups source ~path in
  {
    Obligation.obligations = outcome.obligations @ defaults.obligations;
    holes = List.sort_uniq compare (outcome.holes @ defaults.holes);
    evaluated_constants = outcome.evaluated_constants @ defaults.evaluated_constants;
  }

let prove (lookups : Lookups.t) (key : Resolve.Names.key) =
  let declaration = lookups.interface.names.read_declaration key
  and source = Contracts.read_source_at_key lookups key in
  try
    match declaration.kind with
    | (Function | Method | Test) when Mir.find_code (lookups.mir.read_body_part key) = None -> (
        match Mir.read_defaults lookups.mir key.path with
        | Some { form = _ :: _; _ } ->
            Obligations (Translate.translate_defaults lookups source ~path:key.path)
        | Some { form = []; _ } | None -> Not_proven_here)
    | Theorem -> Obligations (Translate.translate_theorem lookups source ~path:key.path)
    | Function | Method | Test -> (
        let prove_with substitution =
          Translate.translate_function
            ?inherited:(find_inherited_clauses lookups key.path)
            ~substitution lookups source ~path:key.path
        in
        match list_integer_instances lookups key.path with
        | [] ->
            Obligations (add_defaults lookups source key.path (prove_with Types.no_substitution))
        | instances ->
            let outcomes =
              List.map
                (fun (instance, substitution) ->
                  let outcome = prove_with substitution in
                  {
                    outcome with
                    Obligation.obligations =
                      List.map
                        (fun (obligation : Obligation.t) -> { obligation with instance })
                        outcome.obligations;
                  })
                instances
            in
            Obligations
              (add_defaults lookups source key.path
                 {
                   obligations =
                     List.concat_map
                       (fun (outcome : Obligation.outcome) -> outcome.obligations)
                       outcomes;
                   holes =
                     List.sort_uniq compare
                       (List.concat_map
                          (fun (outcome : Obligation.outcome) -> outcome.holes)
                          outcomes);
                   evaluated_constants = [];
                 }))
    | Constant | Member_constant ->
        Obligations (Translate.translate_constant lookups source ~path:key.path)
    | Impl ->
        let outcomes = translate_impl lookups key source in
        Obligations
          {
            obligations =
              List.concat_map (fun (outcome : Obligation.outcome) -> outcome.obligations) outcomes;
            holes = List.concat_map (fun (outcome : Obligation.outcome) -> outcome.holes) outcomes;
            evaluated_constants = [];
          }
    | Type -> (
        let has_defaults () =
          match Mir.read_defaults lookups.mir key.path with
          | Some { form = _ :: _; _ } -> true
          | Some { form = []; _ } | None -> false
        in
        match Mir.read_type_clauses lookups.mir key.path with
        | Some { form = { invariants = _ :: _; _ }; _ } ->
            let outcome = Translate.translate_type lookups source ~path:key.path in
            Obligations
              {
                outcome with
                obligations = outcome.obligations @ translate_derived_default lookups key source;
              }
        | Some { form = { potential; _ }; _ } when Option.is_some potential || has_defaults () ->
            Obligations (Translate.translate_type lookups source ~path:key.path)
        | Some _ | None -> Not_proven_here)
    | Trait | Capability | Law_proof -> Not_proven_here
  with Facts.Unsupported { location; construct; foreign_definition } ->
    Unsupported { location; construct; foreign = foreign_definition }

let show_float bits =
  let spell_shortest ~most ~is_same value =
    let rec spell_digits digits =
      let text = Printf.sprintf "%.*g" digits value in
      if digits >= most || is_same (float_of_string text) then text else spell_digits (digits + 1)
    in
    spell_digits 1
  in
  let text =
    match String.length bits with
    | 64 ->
        let value = Int64.float_of_bits (Int64.of_string ("0b" ^ bits)) in
        spell_shortest ~most:17 ~is_same:(fun read -> read = value) value
    | 32 ->
        let value = Int32.float_of_bits (Int32.of_string ("0b" ^ bits)) in
        spell_shortest ~most:9
          ~is_same:(fun read -> Int32.bits_of_float read = Int32.bits_of_float value)
          value
    | _ -> "a float"
  in
  if text = "nan" || text = "-nan" then "NaN"
  else if text = "inf" then "infinity"
  else if text = "-inf" then "-infinity"
  else if String.contains text '.' then text
  else
    match String.split_first ~sep:"e" text with
    | Some (mantissa, exponent) -> mantissa ^ ".0e" ^ exponent
    | None -> text ^ ".0"

let is_opaque atom = String.contains atom '!'

let show_truss_value members value =
  let show_constructor : Logic.symbol -> string = function
    | Constructor { variant = Some variant; _ } -> variant
    | Constructor { type_ = Named { path = Top { name; _ }; _ }; variant = None } -> name
    | Constructor { type_; variant = None } -> Types.show type_
    | other -> Logic.show_symbol other
  in
  let show_field : Logic.symbol -> string = function
    | Field { field; _ } -> field
    | other -> Logic.show_symbol other
  in
  let parse_bits atom =
    match String.cut_first 2 atom with
    | "#b", digits when digits <> "" -> Some digits
    | "#x", digits when digits <> "" ->
        Some
          (String.concat ""
             (List.map
                (fun digit ->
                  let value = Char.Ascii.hex_digit_to_int digit in
                  String.init 4 (fun index -> if value land (8 lsr index) <> 0 then '1' else '0'))
                (List.of_seq (String.to_seq digits))))
    | _ -> None
  in
  let rec show : Solver.sexp -> string = function
    | List [ Atom "fp"; Atom sign; Atom exponent; Atom fraction ] -> (
        match (parse_bits sign, parse_bits exponent, parse_bits fraction) with
        | Some sign, Some exponent, Some fraction -> show_float (sign ^ exponent ^ fraction)
        | _ -> "a float")
    | List [ Atom "_"; Atom special; Atom _; Atom _ ] -> (
        match special with
        | "+zero" -> "0.0"
        | "-zero" -> "-0.0"
        | "+oo" -> "infinity"
        | "-oo" -> "-infinity"
        | _ -> "NaN")
    | Atom atom when is_opaque atom -> "a value the prover knows nothing more about"
    | Atom atom -> (
        match List.assoc_opt atom members with
        | Some (internal, _) -> show_constructor internal
        | None -> atom)
    | List [ Atom "-"; Atom number ] -> "-" ^ number
    | List (Atom head :: arguments) -> (
        let items = List.map show arguments in
        match List.assoc_opt head members with
        | Some (internal, fields) when List.length fields = List.length items ->
            show_constructor internal ^ "("
            ^ String.concat ", "
                (List.map2 (fun selector item -> show_field selector ^ ": " ^ item) fields items)
            ^ ")"
        | Some (internal, _) -> show_constructor internal ^ "(" ^ String.concat ", " items ^ ")"
        | None -> head ^ "(" ^ String.concat ", " items ^ ")")
    | List (head :: arguments) ->
        show head ^ "(" ^ String.concat ", " (List.map show arguments) ^ ")"
    | List [] -> ""
  in
  show value

let list_counterexample_values members (obligation : Obligation.t) answer_values =
  List.filter_map
    (fun (symbol, name) ->
      match List.assoc_opt symbol answer_values with
      | Some (Solver.Atom atom) when is_opaque atom -> None
      | Some value -> Some (name, show_truss_value members value)
      | None -> None)
    (List.rev obligation.values
    @ List.rev_map (fun (term, name) -> (Logic.Symbol.Named_term term, name)) obligation.locals)

let list_path_notes (obligation : Obligation.t) answer_values =
  List.filter_map Fun.id
    (List.mapi
       (fun index (note, _) ->
         match List.assoc_opt (Logic.Symbol.Reached index) answer_values with
         | Some (Solver.Atom "true") -> Some note
         | _ -> None)
       obligation.path_notes)

type state = {
  site : Catalog.Prover.t;
  is_proven : bool;
  trusts_compiled_code : bool;
  failure : Catalog.Prover.t option;
}

let find_declared_evaluation : Logic.declaration -> Obligation.evaluation option = function
  | Constant (Evaluated evaluation, _) -> Some evaluation
  | Constant _ | Function _ | Datatype _ | Definition _ -> None

let list_evaluations = function
  | Obligations outcome ->
      List.sort_uniq compare
        (List.map (fun path -> Obligation.Constant_value path) outcome.evaluated_constants
        @ List.concat_map
            (fun (obligation : Obligation.t) ->
              List.filter_map find_declared_evaluation obligation.query.declarations)
            outcome.obligations)
  | Unsupported _ | Not_proven_here -> []

type posed_obligation = {
  site : Catalog.Prover.t;
  obligation : Obligation.t;
  query : Logic.query;
  has_run_result : bool;
  failed_runs : Catalog.Prover.failed_run list;
}

let rec state_value (declarations : Logic.declaration list) (term : Logic.term) (sort : Logic.sort)
    (value : Obligation.value) : Logic.term list =
  let raise_bug format = Compiler_bug.raise_bug ~stage:"Prover" format in
  match (sort, value) with
  | Bool, Boolean holds -> [ Logic.equal term (Boolean holds) ]
  | Int, Integer number -> [ Logic.equal term (Integer number) ]
  | Float (exponent, significand), Float number ->
      [ Logic.equal term (Operations.make_float_literal (exponent, significand) number) ]
  | Type_sort _, Elements _ -> []
  | Type_sort ty, Constructed { variant; fields } -> (
      match
        List.find_map
          (function
            | Logic.Datatype (declared, constructors) when Types.equal declared ty ->
                Some constructors
            | Datatype _ | Constant _ | Function _ | Definition _ -> None)
          declarations
      with
      | None | Some [ (Unit, []) ] -> []
      | Some constructors -> (
          match
            List.find_opt
              (fun ((constructor : Logic.symbol), _) ->
                match constructor with
                | Constructor { variant = declared; _ } -> declared = variant
                | _ -> false)
              constructors
          with
          | Some (constructor, selectors) ->
              Logic.Is (constructor, term)
              :: List.concat_map
                   (fun ((selector : Logic.symbol), field_sort) ->
                     match selector with
                     | Field { field; _ } -> (
                         match List.assoc_opt field fields with
                         | Some field_value ->
                             state_value declarations
                               (Logic.Apply (selector, [ term ]))
                               field_sort field_value
                         | None -> raise_bug "an evaluation gave no value for the field %s" field)
                     | _ -> raise_bug "a datatype's selector is not a field")
                   selectors
          | None -> raise_bug "an evaluation gave a variant that `%s` does not have" (Types.show ty)
          ))
  | (Int | Bool | Float _ | Type_sort _ | Function_sort _), _ ->
      raise_bug "an evaluation gave a value of another sort"

let pose_obligation runs site (obligation : Obligation.t) =
  List.fold_left
    (fun posed (declaration : Logic.declaration) ->
      match (declaration, find_declared_evaluation declaration) with
      | Constant (symbol, sort), Some evaluation -> (
          match Evaluation_table.find_opt runs evaluation with
          | Some (Obligation.Evaluated value) -> (
              match state_value obligation.query.declarations (Logic.Symbol symbol) sort value with
              | [] -> posed
              | facts ->
                  {
                    posed with
                    query = { posed.query with facts = posed.query.facts @ facts };
                    has_run_result = true;
                  })
          | Some (Unfinished report | Failed report) ->
              let failed : Catalog.Prover.failed_run =
                match evaluation with
                | Constant_value path -> Constant_run { path; report }
                | Assertion _ -> Assertion_run report
              in
              { posed with failed_runs = posed.failed_runs @ [ failed ] }
          | None -> posed)
      | _ -> posed)
    { site; obligation; query = obligation.query; has_run_result = false; failed_runs = [] }
    obligation.query.declarations

let make_request ({ obligation; query; _ } : posed_obligation) =
  let terms =
    List.map (fun (term, _) -> (Logic.Symbol.Named_term term, term)) obligation.locals
    @ List.concat
        (List.mapi
           (fun index (_, reached) -> [ (Logic.Symbol.Reached index, reached) ])
           obligation.path_notes)
  in
  (Solver.make_request ~symbols:(List.map fst obligation.values) ~terms query, query)

let make_refutation_request ({ query; _ } : posed_obligation) =
  let refutation = { query with goal = Logic.not_ query.goal } in
  (Solver.make_request refutation, refutation)

type posed =
  | Unreadable of Catalog.Prover.t
  | Posed of { obligations : posed_obligation list; failed_evaluations : Catalog.Prover.t list }

let pose ~runs proof =
  let runs = Evaluation_table.of_seq (List.to_seq runs) in
  match proof with
  | Not_proven_here -> Posed { obligations = []; failed_evaluations = [] }
  | Unsupported { location; construct; foreign } ->
      Unreadable (Unreadable { location; construct; foreign })
  | Obligations outcome ->
      Posed
        {
          obligations =
            List.map
              (fun (obligation : Obligation.t) ->
                pose_obligation runs
                  (Proves
                     {
                       location = obligation.location;
                       instance = obligation.instance;
                       obligation = obligation.obligation;
                     })
                  obligation)
              outcome.obligations;
          failed_evaluations =
            List.filter_map
              (fun path ->
                match Evaluation_table.find_opt runs (Constant_value path) with
                | Some (Failed report) -> Some (Catalog.Prover.Unevaluated { path; report })
                | Some (Evaluated _ | Unfinished _) | None -> None)
              outcome.evaluated_constants;
        }

let list_posed = function Unreadable _ -> [] | Posed { obligations; _ } -> obligations
let list_requests posed = List.map make_request (list_posed posed)

let is_refutable (posed : posed_obligation) = function
  | Solver.Counterexample _ -> not posed.obligation.is_rejection
  | Proven | Unknown _ -> false

let list_refutation_requests posed answers =
  List.filter_map
    (fun (obligation, answer) ->
      if is_refutable obligation answer then Some (make_refutation_request obligation) else None)
    (List.combine (list_posed posed) answers)

let explain_failure (posed : posed_obligation) answer ~is_refuted : Catalog.Prover.failure option =
  match answer with
  | Solver.Proven -> None
  | Counterexample _ when is_refuted -> Some Refuted
  | Counterexample values ->
      Some
        (Counterexample
           {
             values =
               list_counterexample_values (Logic.list_members posed.query) posed.obligation values;
             path = list_path_notes posed.obligation values;
             failed_runs = posed.failed_runs;
           })
  | Unknown unknown ->
      Some
        (Undecided
           {
             unknown =
               (match unknown with
               | Solver.Out_of_steps -> Out_of_steps
               | Incomplete reason -> Incomplete reason);
             has_untriggered_fact = posed.obligation.has_untriggered_written_fact;
             failed_runs = posed.failed_runs;
           })

let fail_site failure =
  { site = failure; is_proven = false; trusts_compiled_code = false; failure = Some failure }

let list_states posed ~answers ~refutations =
  match posed with
  | Unreadable failure -> [ fail_site failure ]
  | Posed { obligations; failed_evaluations } ->
      let refutations = Queue.of_seq (List.to_seq refutations) in
      List.map2
        (fun (posed : posed_obligation) answer ->
          let { site; obligation; _ } = posed in
          let is_refuted = is_refutable posed answer && Queue.pop refutations = Solver.Proven in
          let explained = explain_failure posed answer ~is_refuted in
          {
            site;
            is_proven = explained = None;
            trusts_compiled_code = answer = Solver.Proven && posed.has_run_result;
            failure =
              Option.map
                (fun failure ->
                  Catalog.Prover.Unproven
                    {
                      location = obligation.location;
                      instance = obligation.instance;
                      obligation = obligation.obligation;
                      failure;
                      fixes = obligation.fixes;
                      cited =
                        Option.map
                          (fun ((key : Resolve.Names.key), origin) : Catalog.Prover.quoted ->
                            { key; origin })
                          obligation.cited;
                    })
                explained;
          })
        obligations answers
      @ List.map fail_site failed_evaluations

module For_testing = struct
  let list_queries posed =
    List.map
      (fun (obligation : posed_obligation) ->
        (obligation.site, Solver.show_input (make_request obligation)))
      (list_posed posed)
end
