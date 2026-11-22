module Obligation = Obligation
module Lookups = Lookups

module Key_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Resolve.Names.key
end))

module Evaluation_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Obligation.evaluation
end))

type proof =
  | Obligations of Obligation.outcome
  | Unsupported of Obligation.location * string
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
        [ { Obligation.obligations = []; holes; warnings = []; evaluation = None } ]
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
                  ( shown
                    @ [
                        Printf.sprintf "`%s` is `%s`" parameter.name
                          (Language.Builtin_type.show builtin);
                      ],
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
        let message =
          match obligation.code with
          | Invariant ->
              [
                Obligation.Text
                  "The value that the derived `Default` builds from the fields' defaults may not \
                   meet this type's invariant.";
              ]
          | _ -> obligation.message
        in
        { obligation with message })
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
        let warnings = Option.to_list (Unused_run_forever.find lookups key) in
        match list_integer_instances lookups key.path with
        | [] -> Obligations { (prove_with Types.no_substitution) with warnings }
        | instances ->
            let outcomes =
              List.map
                (fun (shown, substitution) ->
                  let outcome = prove_with substitution in
                  let prefix = "Where " ^ String.concat " and " shown ^ ": " in
                  {
                    outcome with
                    Obligation.obligations =
                      List.map
                        (fun (obligation : Obligation.t) ->
                          { obligation with message = Text prefix :: obligation.message })
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
                warnings;
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
            warnings = [];
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
    Unsupported
      ( location,
        match foreign_definition with
        | Some name -> Printf.sprintf "%s, in `%s`" construct name
        | None -> construct )

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

let show_counterexample members (obligation : Obligation.t) answer_values =
  let shown =
    List.filter_map
      (fun (symbol, name) ->
        match List.assoc_opt symbol answer_values with
        | Some (Solver.Atom atom) when is_opaque atom -> None
        | Some value -> Some (Printf.sprintf "`%s` is %s" name (show_truss_value members value))
        | None -> None)
      (List.rev obligation.values
      @ List.rev_map (fun (term, name) -> (Logic.Symbol.Named_term term, name)) obligation.locals)
  in
  let path =
    List.filter_map Fun.id
      (List.mapi
         (fun index (note, _) ->
           match List.assoc_opt (Logic.Symbol.Reached index) answer_values with
           | Some (Solver.Atom "true") -> Some note
           | _ -> None)
         obligation.path_notes)
  in
  (match shown with [] -> "" | shown -> " For example, when " ^ String.concat ", " shown ^ ".")
  ^ match path with [] -> "" | path -> " On that path, " ^ String.concat ", " path ^ "."

let make_diagnostic code span message =
  Diagnostic.make ~code:(Diagnostic.Code.Prover code) span message

let resolve_location (names : Resolve.Names.lookups) (key : Resolve.Names.key)
    (location : Obligation.location) =
  Source.Definition_span.locate (names.read_spans key)
    (match location with
    | Node origin -> Core_walk.locate_origin origin
    | Whole_definition -> (names.read_definition key).id)

let is_word_character character =
  character = '_'
  || (character >= 'a' && character <= 'z')
  || (character >= 'A' && character <= 'Z')
  || (character >= '0' && character <= '9')

let replace_type_names type_names text =
  if type_names = [] then text
  else begin
    let buffer = Buffer.create (String.length text) in
    let length = String.length text in
    let rec scan index =
      if index < length then
        if is_word_character text.[index] then begin
          let stop = ref index in
          while !stop < length && is_word_character text.[!stop] do
            incr stop
          done;
          let word = String.sub text index (!stop - index) in
          Buffer.add_string buffer (Option.value (List.assoc_opt word type_names) ~default:word);
          scan !stop
        end
        else begin
          Buffer.add_char buffer text.[index];
          scan (index + 1)
        end
    in
    scan 0;
    Buffer.contents buffer
  end

let substitute_clause text spans clause replacements type_names =
  let locate origin = Source.Definition_span.locate spans (Core_walk.locate_origin origin) in
  let clause_span = locate clause in
  let clause_text = Facts.quote_span text clause_span in
  let buffer = Buffer.create (String.length clause_text) in
  let next =
    List.fold_left
      (fun next ((span : Source.Definition_span.t), replacement) ->
        let start = span.start - clause_span.start and stop = span.stop - clause_span.start in
        if start < next || stop > String.length clause_text then next
        else begin
          Buffer.add_string buffer
            (replace_type_names type_names (String.sub clause_text next (start - next)));
          Buffer.add_string buffer replacement;
          stop
        end)
      0
      (List.sort_uniq compare
         (List.map (fun (origin, replacement) -> (locate origin, replacement)) replacements))
  in
  Buffer.add_string buffer (replace_type_names type_names (String.drop_first next clause_text));
  Buffer.contents buffer

let render (lookups : Lookups.t) (message : Obligation.message) =
  String.concat ""
    (List.map
       (function
         | Obligation.Text text -> text
         | Quote (key, origin) ->
             Facts.quote_span
               (lookups.interface.names.read_text key)
               (Source.Definition_span.locate
                  (lookups.interface.names.read_spans key)
                  (Core_walk.locate_origin origin))
         | Substituted { key; clause; replacements; type_names } ->
             substitute_clause
               (lookups.interface.names.read_text key)
               (lookups.interface.names.read_spans key)
               clause replacements type_names)
       message)

let render_fix lookups ({ title; edits } : Obligation.fix) =
  Diagnostic.fix (render lookups title)
    (List.map
       (fun ({ at; replacement } : Obligation.edit) ->
         Diagnostic.replace at (render lookups replacement))
       edits)

let locate_citation (lookups : Lookups.t) ((key : Resolve.Names.key), origin) =
  let place = lookups.interface.names.read_place key in
  ( place,
    Source.Definition_span.to_file ~base:place.base
      (Source.Definition_span.locate
         (lookups.interface.names.read_spans key)
         (Core_walk.locate_origin origin)) )

type 'span site = { code : Diagnostic.Code.prover; span : 'span; shows : string }

type 'span state = {
  site : 'span site;
  failure : 'span Diagnostic.diagnostic option;
  trusts_compiled_code : bool;
}

type verdict = (Source.Definition_span.t state * (Resolve.Names.key * Core.origin) option) list

let explain_unknown = function
  | Solver.Out_of_steps ->
      " The solver reached its step limit before it found a proof or a counterexample."
  | Incomplete reason ->
      Printf.sprintf
        " The solver's decision procedures are incomplete for this query, so it stopped without a \
         proof or a counterexample. Z3 gives the reason `%s`."
        reason

let find_declared_evaluation : Logic.declaration -> Obligation.evaluation option = function
  | Constant (Template_check { function_; literals }, _) ->
      Some (Template_check { function_; literals })
  | Constant (Evaluated_constant path, _) -> Some (Constant_value path)
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

type posed = {
  site : Source.Definition_span.t site;
  obligation : Obligation.t;
  query : Logic.query;
  has_run_result : bool;
  failed_runs : (Obligation.evaluation * string) list;
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
              { posed with failed_runs = posed.failed_runs @ [ (evaluation, report) ] }
          | None -> posed)
      | _ -> posed)
    { site; obligation; query = obligation.query; has_run_result = false; failed_runs = [] }
    obligation.query.declarations

let make_request ({ obligation; query; _ } : posed) =
  let terms =
    List.map (fun (term, _) -> (Logic.Symbol.Named_term term, term)) obligation.locals
    @ List.concat
        (List.mapi
           (fun index (_, reached) -> [ (Logic.Symbol.Reached index, reached) ])
           obligation.path_notes)
  in
  (Solver.make_request ~symbols:(List.map fst obligation.values) ~terms query, query)

let make_refutation_request ({ query; _ } : posed) =
  let refutation = { query with goal = Logic.not_ query.goal } in
  (Solver.make_request refutation, refutation)

type posed_proof =
  | Unreadable of Source.Definition_span.t site
  | Posed of { obligations : posed list; failed_evaluation : Source.Definition_span.t site option }

let pose_proof (lookups : Lookups.t) runs key proof =
  let resolve location = resolve_location lookups.interface.names key location in
  match proof with
  | Not_proven_here -> Posed { obligations = []; failed_evaluation = None }
  | Unsupported (location, construct) ->
      Unreadable
        {
          code = Unsupported;
          span = resolve location;
          shows =
            Printf.sprintf "The prover cannot read %s yet, so nothing in this definition is proven."
              construct;
        }
  | Obligations outcome ->
      Posed
        {
          obligations =
            List.map
              (fun (obligation : Obligation.t) ->
                pose_obligation runs
                  {
                    code = obligation.code;
                    span = resolve obligation.location;
                    shows = render lookups obligation.message;
                  }
                  obligation)
              outcome.obligations;
          failed_evaluation =
            Option.bind outcome.evaluation (fun (evaluation : Obligation.evaluation) ->
                match (evaluation, Evaluation_table.find_opt runs evaluation) with
                | Constant_value path, Some (Failed report) ->
                    Some
                      {
                        code = Evaluation;
                        span = resolve Whole_definition;
                        shows =
                          Printf.sprintf "The value of `%s` cannot be computed: %s" (Path.show path)
                            report;
                      }
                | Constant_value _, (Some (Evaluated _ | Unfinished _) | None) -> None
                | Template_check _, _ ->
                    Compiler_bug.raise_bug ~stage:"Prover"
                      "a definition's own evaluation is a template check");
        }

let pose_proofs ~runs lookups proofs =
  let runs = Evaluation_table.of_seq (List.to_seq runs) in
  List.map (fun (key, proof) -> (key, pose_proof lookups runs key proof)) proofs

let list_posed = function Unreadable _ -> [] | Posed { obligations; _ } -> obligations

let explain_failed_runs failed_runs =
  String.concat ""
    (List.map
       (fun ((evaluation : Obligation.evaluation), report) ->
         match evaluation with
         | Template_check { function_; literals } ->
             Printf.sprintf
               " Running `%s` on the template text `%s` failed, so its result is not known: %s"
               (Facts.show_callee function_) (String.concat "${...}" literals) report
         | Constant_value path ->
             Printf.sprintf " The evaluation of `%s` stopped, so its value is not known: %s"
               (Path.show path) report)
       failed_runs)

let make_state (lookups : Lookups.t) (posed : posed) answer ~is_refuted =
  let { site; obligation; _ } = posed in
  let others =
    match site.code with
    | Overflow | Division | Shift ->
        " It can also be checked first with an `if`, or done with the checked operation."
    | Out_of_bounds ->
        " It can also be checked first with an `if`, or, for one element, read with `get`."
    | _ -> ""
  in
  let find_failure explained =
    Some
      {
        (make_diagnostic site.code site.span (site.shows ^ explained ^ others)) with
        fixes = List.map (render_fix lookups) obligation.fixes;
      }
  in
  ( {
      site;
      failure =
        (match answer with
        | Solver.Proven -> None
        | Counterexample _ when is_refuted ->
            find_failure " This fails every time the code reaches it."
        | Counterexample values ->
            find_failure
              (show_counterexample (Logic.list_members posed.query) obligation values
              ^ explain_failed_runs posed.failed_runs)
        | Unknown unknown ->
            find_failure
              (explain_unknown unknown
             ^ " If the code is correct, a `proof` block or a theorem can lead the solver to the \
                proof."
              ^ (if obligation.has_untriggered_written_fact then
                   " A quantified fact in the query has no trigger, so an `assert` of that fact at \
                    the term the proof needs may be enough."
                 else "")
              ^ explain_failed_runs posed.failed_runs));
      trusts_compiled_code = answer = Proven && posed.has_run_result;
    },
    obligation.cited )

type warnings = {
  lookups : Lookups.t;
  table : Source.Definition_span.t Diagnostic.diagnostic list Key_table.t;
}

let collect_warnings lookups proofs =
  let table = Key_table.create (List.length proofs) in
  List.iter
    (fun (key, proof) ->
      match proof with
      | Obligations outcome when outcome.Obligation.warnings <> [] ->
          Key_table.replace table key outcome.warnings
      | Obligations _ | Unsupported _ | Not_proven_here -> ())
    proofs;
  { lookups; table }

type verdicts = { lookups : Lookups.t; verdicts : verdict Key_table.t; warnings : warnings }

let decide ~runs lookups solver proofs =
  let posed_proofs = pose_proofs ~runs lookups proofs in
  let posed = List.concat_map (fun (_, posed_proof) -> list_posed posed_proof) posed_proofs in
  let answers = Solver.solve_all solver (List.map make_request posed) in
  let is_refutable (posed : posed) = function
    | Solver.Counterexample _ -> not posed.obligation.is_rejection
    | Proven | Unknown _ -> false
  in
  let countered =
    List.filter_map
      (fun (posed, answer) -> if is_refutable posed answer then Some posed else None)
      (List.combine posed answers)
  in
  let refutations =
    Queue.of_seq
      (List.to_seq (Solver.solve_all solver (List.map make_refutation_request countered)))
  in
  let decided =
    Queue.of_seq
      (List.to_seq
         (List.map2
            (fun posed answer ->
              let is_refuted = is_refutable posed answer && Queue.pop refutations = Solver.Proven in
              (posed, answer, is_refuted))
            posed answers))
  in
  let verdicts = Key_table.create (List.length proofs) in
  let warnings = collect_warnings lookups proofs in
  List.iter
    (fun (key, posed_proof) ->
      Key_table.replace verdicts key
        (match posed_proof with
        | Unreadable site ->
            [
              ( {
                  site;
                  failure = Some (make_diagnostic site.code site.span site.shows);
                  trusts_compiled_code = false;
                },
                None );
            ]
        | Posed { obligations; failed_evaluation } ->
            List.map
              (fun _ ->
                let posed, answer, is_refuted = Queue.pop decided in
                make_state lookups posed answer ~is_refuted)
              obligations
            @ List.map
                (fun site ->
                  ( {
                      site;
                      failure = Some (make_diagnostic site.code site.span site.shows);
                      trusts_compiled_code = false;
                    },
                    None ))
                (Option.to_list failed_evaluation)))
    posed_proofs;
  { lookups; verdicts; warnings }

let list_file_definitions (lookups : Lookups.t) table file =
  List.filter_map
    (fun (declaration : Resolve.Names.declaration) ->
      let key = declaration.key in
      Option.map
        (fun recorded -> ((lookups.interface.names.read_place key).base, recorded))
        (Key_table.find_opt table key))
    (lookups.interface.names.list_declarations_in file)

let locate_site ~base site = { site with span = Source.Definition_span.to_file ~base site.span }

let list_file_states { lookups; verdicts; _ } file =
  List.map
    (fun (base, verdict) ->
      List.map
        (fun ((state : Source.Definition_span.t state), cited) ->
          let cited = Option.map (locate_citation lookups) cited in
          let note =
            match cited with
            | Some ((place : Resolve.Names.place), span) when place.file = file ->
                Some (span, "This is the clause that must hold.")
            | _ -> None
          in
          let elsewhere =
            match cited with
            | Some ((place : Resolve.Names.place), span) when place.file <> file -> (
                match lookups.read_source place.file with
                | source ->
                    let line, _ = Source.compute_position source span.start in
                    Printf.sprintf " The clause that must hold is at `%s:%d`." (Source.path source)
                      line
                | exception Not_found -> "")
            | _ -> ""
          in
          {
            state with
            site = locate_site ~base state.site;
            failure =
              Option.map
                (fun failure ->
                  let failure =
                    Diagnostic.map_spans (Source.Definition_span.to_file ~base) failure
                  in
                  let failure = { failure with message = failure.message ^ elsewhere } in
                  match note with
                  | Some note -> { failure with notes = failure.notes @ [ note ] }
                  | None -> failure)
                state.failure;
          })
        verdict)
    (list_file_definitions lookups verdicts file)

let compare_sites left right = compare (left.span, left.code) (right.span, right.code)

let sort_diagnostics list =
  List.sort
    (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare (left.span, left.code) (right.span, right.code))
    list

let list_states verdicts file =
  List.concat (list_file_states verdicts file)
  |> List.sort (fun (left : Source.span state) (right : Source.span state) ->
      compare_sites left.site right.site)

let list_warnings { lookups; table } file =
  List.concat_map
    (fun (base, warnings) ->
      List.map (Diagnostic.map_spans (Source.Definition_span.to_file ~base)) warnings)
    (list_file_definitions lookups table file)

let list_diagnostics verdicts file =
  List.concat_map
    (fun states ->
      List.fold_left
        (fun (reported, diagnostics) state ->
          match state.failure with
          | Some failure when not (List.mem (state.site.code, state.site.shows) reported) ->
              ((state.site.code, state.site.shows) :: reported, failure :: diagnostics)
          | _ -> (reported, diagnostics))
        ([], []) states
      |> snd)
    (list_file_states verdicts file)
  |> List.append (list_warnings verdicts.warnings file)
  |> sort_diagnostics

module For_testing = struct
  let list_queries ~runs lookups proofs file =
    List.concat_map
      (fun (base, posed_proof) ->
        List.map
          (fun (posed : posed) ->
            (locate_site ~base posed.site, Solver.show_input (make_request posed)))
          (list_posed posed_proof))
      (list_file_definitions lookups
         (Key_table.of_seq (List.to_seq (pose_proofs ~runs lookups proofs)))
         file)
    |> List.sort (fun (left, _) (right, _) -> compare_sites left right)
end
