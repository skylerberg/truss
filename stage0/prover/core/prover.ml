module Obligation = Obligation
module Lookups = Lookups

module Key_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Resolve.Names.key
end))

module Template_check_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Obligation.template_check
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

let translate_impl_laws (lookups : Lookups.t) (key : Resolve.Names.key) source =
  let interface = Interface.Definition.read_impl_interface lookups.interface key.path in
  if Contracts.is_impl_unfinished lookups key then []
  else
    [
      Translate.translate_laws lookups source ~impl:key.path ~trait:interface.implements
        ~for_type:interface.for_type
        ~proofs:
          (Contracts.list_law_proofs lookups (Path.locate_package key.path) interface.implements
             interface.for_type)
        ~at:Whole_definition;
    ]

let is_specification_module (key : Resolve.Names.key) = key.module_ = Well_known.specification

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
                          (Intrinsic.show_builtin builtin);
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
    Path.Method
      {
        owner = Derived { type_ = key.path; trait = Well_known.make_path Default };
        name = "default";
        receiver = Static;
      }
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
          | _ -> Text "In the derived `Default`: " :: obligation.message
        in
        { obligation with location = Whole_definition; message })
      outcome.obligations
  else []

let prove (lookups : Lookups.t) (key : Resolve.Names.key) =
  match
    (lookups.interface.names.read_declaration key, Contracts.read_source_at_key lookups key)
  with
  | _ when is_specification_module key -> Not_proven_here
  | declaration, source -> (
      lookups.read_patterns key;
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
                        (List.concat_map
                           (fun (outcome : Obligation.outcome) -> outcome.holes)
                           outcomes);
                  })
        | Constant -> Obligations (Translate.translate_constant lookups source ~path:key.path)
        | Impl ->
            let outcomes = translate_impl_laws lookups key source in
            Obligations
              {
                obligations =
                  List.concat_map
                    (fun (outcome : Obligation.outcome) -> outcome.obligations)
                    outcomes;
                holes =
                  List.concat_map (fun (outcome : Obligation.outcome) -> outcome.holes) outcomes;
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
            | Some { form = { potential; _ }; _ } when Option.is_some potential || has_defaults ()
              ->
                Obligations (Translate.translate_type lookups source ~path:key.path)
            | Some _ | None -> Not_proven_here)
        | Trait | Capability | Member_constant | Law_proof -> Not_proven_here
      with Facts.Unsupported { location; construct; foreign_definition } ->
        Unsupported
          ( location,
            match foreign_definition with
            | Some name -> Printf.sprintf "%s, in `%s`" construct name
            | None -> construct ))

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
         (fun index (holding, failing, _, _) ->
           match
             ( List.assoc_opt (Logic.Symbol.Reached index) answer_values,
               List.assoc_opt (Logic.Symbol.Condition index) answer_values )
           with
           | Some (Solver.Atom "true"), Some (Solver.Atom "true") -> Some holding
           | Some (Solver.Atom "true"), Some (Solver.Atom "false") -> failing
           | _ -> None)
         obligation.decisions)
  in
  (match shown with [] -> "" | shown -> " For example, when " ^ String.concat ", " shown ^ ".")
  ^ match path with [] -> "" | path -> " On that path, " ^ String.concat ", " path ^ "."

let make_diagnostic code span message =
  Diagnostic.make ~code:(Diagnostic.Code.Prover code) span message

let resolve_location (names : Resolve.Names.lookups) (key : Resolve.Names.key)
    (location : Obligation.location) =
  Source.Definition_span.locate (names.read_spans key)
    (match location with
    | Node origin -> origin
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
  let clause_span = Source.Definition_span.locate spans clause in
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
         (List.map
            (fun (origin, replacement) -> (Source.Definition_span.locate spans origin, replacement))
            replacements))
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
               (Source.Definition_span.locate (lookups.interface.names.read_spans key) origin)
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
      (Source.Definition_span.locate (lookups.interface.names.read_spans key) origin) )

type answer = Solved of Solver.answer | Ran of bool | Run_failed of string

type 'span state = {
  code : Diagnostic.Code.prover;
  span : 'span;
  shows : string;
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

let list_definition_states (lookups : Lookups.t) (key : Resolve.Names.key) proof answers =
  let resolve location = resolve_location lookups.interface.names key location in
  match proof with
  | Not_proven_here -> []
  | Unsupported (location, construct) ->
      let message =
        Printf.sprintf "The prover cannot read %s yet, so nothing in this definition is proven."
          construct
      in
      [
        ( {
            code = Unsupported;
            span = resolve location;
            shows = message;
            failure = Some (make_diagnostic Unsupported (resolve location) message);
            trusts_compiled_code = false;
          },
          None );
      ]
  | Obligations outcome ->
      List.map2
        (fun (obligation : Obligation.t) answer ->
          let span = resolve obligation.location in
          let message = render lookups obligation.message in
          let others =
            match obligation.code with
            | Overflow | Division | Shift ->
                " It can also be checked first with an `if`, or done with the checked operation."
            | _ -> ""
          in
          let find_failure explained =
            Some
              {
                (make_diagnostic obligation.code span (message ^ explained ^ others)) with
                fixes = List.map (render_fix lookups) obligation.fixes;
              }
          in
          ( {
              code = obligation.code;
              span;
              shows = message;
              failure =
                (match answer with
                | Solved Proven | Ran true -> None
                | Ran false -> find_failure " Running it on this template's text gives `false`."
                | Run_failed report ->
                    find_failure
                      (" Running it on this template's text failed, so it is not known: " ^ report)
                | Solved (Counterexample values) ->
                    find_failure
                      (show_counterexample (Logic.list_members obligation.query) obligation values)
                | Solved (Unknown unknown) ->
                    find_failure
                      (explain_unknown unknown
                     ^ " If the code is correct, a `proof` block or a theorem can lead the solver \
                        to the proof."
                      ^
                      if Logic.has_untriggered_fact obligation.query then
                        " A quantified fact in the query has no trigger, so an `assert` of that \
                         fact at the term the proof needs may be enough."
                      else ""));
              trusts_compiled_code = (match answer with Ran true -> true | _ -> false);
            },
            obligation.cited ))
        outcome.obligations answers

let make_request (obligation : Obligation.t) =
  let terms =
    List.map (fun (term, _) -> (Logic.Symbol.Named_term term, term)) obligation.locals
    @ List.concat
        (List.mapi
           (fun index (_, _, reached, condition) ->
             [ (Logic.Symbol.Reached index, reached); (Logic.Symbol.Condition index, condition) ])
           obligation.decisions)
  in
  ( Solver.make_request ~symbols:(List.map fst obligation.values) ~terms obligation.query,
    obligation.query )

type question = Decided of answer | Asked of (Solver.request * Logic.query)

let run_answer runs ({ check; clause } : Obligation.template_clause) =
  Option.map
    (function
      | Ok holds -> Ran (List.assoc clause (List.combine check.clauses holds))
      | Error report -> Run_failed report)
    (Template_check_table.find_opt runs check)

type verdicts = { lookups : Lookups.t; verdicts : verdict Key_table.t }

let decide ~runs lookups solver proofs =
  let runs = Template_check_table.of_seq (List.to_seq runs) in
  let make_question (obligation : Obligation.t) =
    match Option.bind obligation.template_clause (run_answer runs) with
    | Some answer -> Decided answer
    | None -> Asked (make_request obligation)
  in
  let questions =
    List.map
      (fun (key, proof) ->
        let obligations =
          match proof with
          | Obligations (outcome : Obligation.outcome) -> outcome.obligations
          | Unsupported _ | Not_proven_here -> []
        in
        (key, proof, List.map make_question obligations))
      proofs
  in
  let solved =
    Queue.of_seq
      (List.to_seq
         (Solver.solve_all solver
            (List.concat_map
               (fun (_, _, questions) ->
                 List.filter_map
                   (function Asked asked -> Some asked | Decided _ -> None)
                   questions)
               questions)))
  in
  let verdicts = Key_table.create (List.length proofs) in
  List.iter
    (fun (key, proof, questions) ->
      let answers =
        List.map
          (function Decided answer -> answer | Asked _ -> Solved (Queue.pop solved))
          questions
      in
      Key_table.replace verdicts key (list_definition_states lookups key proof answers))
    questions;
  { lookups; verdicts }

let list_file_states { lookups; verdicts } file =
  let read_verdict key = Option.value (Key_table.find_opt verdicts key) ~default:[] in
  List.map
    (fun declaration ->
      let key = Resolve.Names.make_key declaration in
      let ({ base; _ } : Resolve.Names.place) = lookups.interface.names.read_place key in
      List.map
        (fun (state, cited) ->
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
            span = Source.Definition_span.to_file ~base state.span;
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
        (read_verdict key))
    (lookups.interface.names.list_declarations_in file)

let sort_diagnostics list =
  List.sort
    (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare (left.span, left.code) (right.span, right.code))
    list

let list_states verdicts file =
  List.concat (list_file_states verdicts file)
  |> List.sort (fun left right -> compare (left.span, left.code) (right.span, right.code))

let list_diagnostics verdicts file =
  List.concat_map
    (fun states ->
      List.fold_left
        (fun (reported, diagnostics) state ->
          match state.failure with
          | Some failure when not (List.mem (state.code, state.shows) reported) ->
              ((state.code, state.shows) :: reported, failure :: diagnostics)
          | _ -> (reported, diagnostics))
        ([], []) states
      |> snd)
    (list_file_states verdicts file)
  |> sort_diagnostics

module For_testing = struct
  type query = { code : Diagnostic.Code.prover; span : Source.span; shows : string; input : string }

  let list_queries (lookups : Lookups.t) proofs file =
    let proofs = Key_table.of_seq (List.to_seq proofs) in
    List.concat_map
      (fun declaration ->
        let key = Resolve.Names.make_key declaration in
        match Key_table.find_opt proofs key with
        | Some (Obligations outcome) ->
            let ({ base; _ } : Resolve.Names.place) = lookups.interface.names.read_place key in
            List.map
              (fun (obligation : Obligation.t) ->
                {
                  code = obligation.code;
                  span =
                    Source.Definition_span.to_file ~base
                      (resolve_location lookups.interface.names key obligation.location);
                  shows = render lookups obligation.message;
                  input = Solver.show_input (make_request obligation);
                })
              outcome.obligations
        | Some (Unsupported _ | Not_proven_here) | None -> [])
      (lookups.interface.names.list_declarations_in file)
    |> List.sort (fun left right -> compare (left.span, left.code) (right.span, right.code))
end
