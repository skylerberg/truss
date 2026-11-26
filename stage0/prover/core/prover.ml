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
      foreign : Path.t option;
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
        [ { Obligation.obligations = []; holes; evaluation = None } ]
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

let prove (lookups : Lookups.t) (key : Resolve.Names.key) =
  let declaration = lookups.interface.names.read_declaration key
  and source = Contracts.read_source_at_key lookups key in
  try
    match declaration.kind with
    | (Function | Method | Test) when Mir.find_code (lookups.mir.read_body_part key) = None ->
        Not_proven_here
    | Theorem -> Obligations (Translate.translate_theorem lookups source ~path:key.path)
    | Function | Method | Test -> (
        let prove_with substitution =
          Translate.translate_function
            ?inherited:(find_inherited_clauses lookups key.path)
            ~substitution lookups source ~path:key.path
        in
        match list_integer_instances lookups key.path with
        | [] -> Obligations (prove_with Types.no_substitution)
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
              {
                obligations =
                  List.concat_map
                    (fun (outcome : Obligation.outcome) -> outcome.obligations)
                    outcomes;
                holes =
                  List.sort_uniq compare
                    (List.concat_map (fun (outcome : Obligation.outcome) -> outcome.holes) outcomes);
                evaluation = None;
              })
    | Constant | Member_constant ->
        Obligations (Translate.translate_constant lookups source ~path:key.path)
    | Impl ->
        let outcomes = translate_impl lookups key source in
        Obligations
          {
            obligations =
              List.concat_map (fun (outcome : Obligation.outcome) -> outcome.obligations) outcomes;
            holes = List.concat_map (fun (outcome : Obligation.outcome) -> outcome.holes) outcomes;
            evaluation = None;
          }
    | Type -> (
        let has_defaults () =
          match Mir.read_defaults lookups.mir key.path with
          | Some { form = Field_defaults (_ :: _); _ } -> true
          | Some { form = Field_defaults [] | Parameter_defaults _; _ } | None -> false
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

let is_opaque atom = String.contains atom '!'

let read_bit_vector atom =
  let fold_digits ~digit_width digits =
    String.fold_left
      (fun value digit ->
        Int64.logor
          (Int64.shift_left value digit_width)
          (Int64.of_int (Char.Ascii.hex_digit_to_int digit)))
      0L digits
  in
  match String.cut_first 2 atom with
  | "#b", digits when digits <> "" -> (fold_digits ~digit_width:1 digits, String.length digits)
  | "#x", digits when digits <> "" -> (fold_digits ~digit_width:4 digits, 4 * String.length digits)
  | _ -> Facts.raise_bug "the model gives `%s` for the bits of a float" atom

let read_float sign exponent fraction : Catalog.Model_value.t =
  let sign, _ = read_bit_vector sign
  and exponent, exponent_width = read_bit_vector exponent
  and fraction, fraction_width = read_bit_vector fraction in
  let bits =
    Int64.logor
      (Int64.shift_left sign (exponent_width + fraction_width))
      (Int64.logor (Int64.shift_left exponent fraction_width) fraction)
  in
  match 1 + exponent_width + fraction_width with
  | 64 -> Float { value = Int64.float_of_bits bits; is_single = false }
  | 32 -> Float { value = Int32.float_of_bits (Int64.to_int32 bits); is_single = true }
  | width -> Facts.raise_bug "the model gives a float of %d bits" width

let read_special_float special exponent_width : Catalog.Model_value.t =
  let value =
    match special with
    | "+zero" -> 0.0
    | "-zero" -> -0.0
    | "+oo" -> Float.infinity
    | "-oo" -> Float.neg_infinity
    | "NaN" -> Float.nan
    | _ -> Facts.raise_bug "the model gives the float `%s`" special
  in
  Float { value; is_single = exponent_width = "8" }

let make_constructed (constructor : Logic.symbol) fields : Catalog.Model_value.t =
  match constructor with
  | Constructor { variant = Some variant; _ } -> Variant_value { variant; fields }
  | Constructor { type_; variant = None } -> Record_value { type_; fields }
  | Unit -> Unit_value
  | other -> Facts.raise_bug "the model constructs a value with %s" (Logic.show_symbol other)

let read_selector : Logic.symbol -> string = function
  | Field { field; _ } -> field
  | other -> Facts.raise_bug "the model selects a field with %s" (Logic.show_symbol other)

let find_natural atom =
  if atom <> "" && String.for_all Char.Ascii.is_digit atom then Some (Z.of_string atom) else None

let rec expand_lets bindings : Solver.sexp -> Solver.sexp = function
  | List [ Atom "let"; List definitions; body ] ->
      let bind scope : Solver.sexp -> (string * Solver.sexp) list = function
        | List [ Atom name; value ] -> (name, expand_lets bindings value) :: scope
        | _ -> Facts.raise_bug "the model binds a `let` without a name and a value"
      in
      expand_lets (List.fold_left bind bindings definitions) body
  | Atom atom as term -> Option.value (List.assoc_opt atom bindings) ~default:term
  | List terms -> List (List.map (expand_lets bindings) terms)

let rec read_model_value members : Solver.sexp -> Catalog.Model_value.t = function
  | List [ Atom "let"; _; _ ] as term -> read_model_value members (expand_lets [] term)
  | List [ Atom "fp"; Atom sign; Atom exponent; Atom fraction ] -> read_float sign exponent fraction
  | List [ Atom "_"; Atom special; Atom exponent_width; Atom _ ] ->
      read_special_float special exponent_width
  | Atom atom when is_opaque atom -> Unknown
  | Atom "true" -> Boolean true
  | Atom "false" -> Boolean false
  | Atom atom -> (
      match (List.assoc_opt atom members, find_natural atom) with
      | Some (constructor, _), _ -> make_constructed constructor []
      | None, Some value -> Integer value
      | None, None -> Facts.raise_bug "the model gives the atom `%s`" atom)
  | List [ Atom "-"; Atom number ] -> (
      match find_natural number with
      | Some value -> Integer (Z.neg value)
      | None -> Facts.raise_bug "the model negates `%s`" number)
  | List (Atom head :: arguments) -> (
      match List.assoc_opt head members with
      | Some (constructor, selectors) when List.length selectors = List.length arguments ->
          make_constructed constructor
            (List.map2
               (fun selector argument : Catalog.Model_value.field ->
                 { field = read_selector selector; value = read_model_value members argument })
               selectors arguments)
      | Some _ -> Facts.raise_bug "the model gives `%s` the wrong number of fields" head
      | None -> Facts.raise_bug "the model applies `%s`, which constructs no value" head)
  | List _ ->
      Facts.raise_bug "the model gives a value that is neither a constant nor a construction"

let list_counterexample_values members (obligation : Obligation.t) answer_values =
  List.filter_map
    (fun (symbol, name) ->
      match List.assoc_opt symbol answer_values with
      | Some (Solver.Atom atom) when is_opaque atom -> None
      | Some value -> Some (name, read_model_value members value)
      | None -> None)
    (List.rev obligation.values
    @ List.rev_map (fun (term, name) -> (Logic.Symbol.Named_term term, name)) obligation.locals)

let list_path_notes (obligation : Obligation.t) answer_values =
  let is_shown_with_its_value (term, value) =
    let shown_as =
      match term with
      | Logic.Symbol symbol when List.mem_assoc symbol obligation.values -> Some symbol
      | _ when List.mem_assoc term obligation.locals -> Some (Logic.Symbol.Named_term term)
      | _ -> None
    in
    Option.bind shown_as (fun symbol -> List.assoc_opt symbol answer_values)
    = Some (Solver.Atom (string_of_bool value))
  in
  List.filter_map Fun.id
    (List.mapi
       (fun index (noted : Obligation.noted_path) ->
         match List.assoc_opt (Logic.Symbol.Reached index) answer_values with
         | Some (Solver.Atom "true")
           when not (Option.fold ~none:false ~some:is_shown_with_its_value noted.tested) ->
             Some noted.note
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
        (Option.to_list outcome.evaluation
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
          | Some (Unfinished stop | Failed stop) ->
              let failed : Catalog.Prover.failed_run =
                match evaluation with
                | Constant_value path -> Constant_run { path; stop }
                | Assertion _ -> Assertion_run stop
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
           (fun index (noted : Obligation.noted_path) ->
             [ (Logic.Symbol.Reached index, noted.reached) ])
           obligation.path_notes)
  in
  Solver.make_request ~symbols:(List.map fst obligation.values) ~terms query

let make_refutation_request ({ query; _ } : posed_obligation) =
  Solver.make_request { query with goal = Logic.not_ query.goal }

type posed =
  | Unreadable of Catalog.Prover.t
  | Posed of { obligations : posed_obligation list; failed_evaluation : Catalog.Prover.t option }

let pose ~runs proof =
  let runs = Evaluation_table.of_seq (List.to_seq runs) in
  match proof with
  | Not_proven_here -> Posed { obligations = []; failed_evaluation = None }
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
          failed_evaluation =
            Option.bind outcome.evaluation (fun (evaluation : Obligation.evaluation) ->
                match (evaluation, Evaluation_table.find_opt runs evaluation) with
                | Constant_value path, Some (Failed stop) ->
                    Some (Catalog.Prover.Unevaluated { path; stop })
                | Constant_value _, (Some (Evaluated _ | Unfinished _) | None) -> None
                | Assertion _, _ ->
                    Compiler_bug.raise_bug ~stage:"Prover"
                      "a definition's own evaluation is not of a constant");
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
  | Posed { obligations; failed_evaluation } ->
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
      @ List.map fail_site (Option.to_list failed_evaluation)

module For_testing = struct
  let list_queries posed =
    List.map
      (fun (obligation : posed_obligation) ->
        (obligation.site, Solver.show_input (make_request obligation)))
      (list_posed posed)
end
