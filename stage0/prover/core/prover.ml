module State = State
module Facts = Facts
module Contracts = Contracts
module Lookups = Lookups

module Key_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Resolve.Names.key
end))

module Template_check_table = Hashtbl.Make (Structural_key.Make (struct
  type t = State.template_check
end))

type proof =
  | Obligations of State.outcome
  | Unsupported of State.location * string
  | Not_proven_here

let find_inherited_part (lookups : Lookups.t) (path : Path.t) =
  match path with
  | Method { owner = impl; name; receiver } -> (
      match Interface.Definition.read_interface lookups.interface impl with
      | Some (Interface.Environment.Impl_interface interface) -> (
          let implemented = interface.implements.trait in
          let substitution =
            Option.value ~default:[] (Interface.Impls.make_impl_substitution lookups.interface impl)
          in
          match Contracts.find_trait_part lookups implemented name receiver with
          | Some part -> Some (part, substitution)
          | None ->
              Option.map
                (fun part -> (part, substitution))
                (Contracts.find_capability_part lookups implemented name))
      | _ -> None)
  | _ -> None

let translate_impl_laws (lookups : Lookups.t) (key : Resolve.Names.key) source =
  match Interface.Definition.read_interface lookups.interface key.path with
  | Some (Interface.Environment.Impl_interface interface)
    when not (Contracts.is_impl_unfinished lookups key) ->
      [
        Translate.translate_laws lookups source ~impl:key.path ~trait:interface.implements
          ~for_type:interface.for_type
          ~proofs:
            (Contracts.list_law_proofs lookups (Path.package key.path) interface.implements
               interface.for_type)
          ~at:Whole_definition;
      ]
  | _ -> []

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
            | Value_generic | Capability_generic -> None)
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
                          (Intrinsic.builtin_name builtin);
                      ],
                    (parameter, Types.Type (Types.make_builtin builtin)) :: substitution ))
                builtins)
            instances)
    [ ([], []) ]
    (self @ generics)
  |> List.filter (fun (shown, _) -> shown <> [])

let translate_derived_default (lookups : Lookups.t) (key : Resolve.Names.key)
    (source : State.source) =
  let derives_default =
    match Interface.Definition.read_interface lookups.interface key.path with
    | Some (Interface.Environment.Type_interface interface) ->
        List.exists (Well_known.is Default) interface.derives
    | _ -> false
  in
  let path =
    Path.Method
      {
        owner = Derived { type_ = key.path; trait = Well_known.path Default };
        name = "default";
        receiver = Static;
      }
  in
  if derives_default && Option.is_some (Mir.read_code lookups.mir path) then
    let outcome = Translate.translate_function lookups source ~path in
    List.map
      (fun (obligation : State.obligation) ->
        let message =
          match obligation.code with
          | Invariant ->
              [
                State.Text
                  "The value that the derived `Default` builds from the fields' defaults may not \
                   meet this type's invariant.";
              ]
          | _ -> Text "In the derived `Default`: " :: obligation.message
        in
        { obligation with location = Whole_definition; message })
      outcome.obligations
  else []

let prove (lookups : Lookups.t) (key : Resolve.Names.key) =
  match (lookups.interface.names.declaration key, Contracts.read_source_at_key lookups key) with
  | _ when is_specification_module key -> Not_proven_here
  | declaration, source -> (
      lookups.patterns key;
      try
        match declaration.kind with
        | (Function | Method) when Mir.find_code (lookups.mir.body_part key) = None ->
            Not_proven_here
        | Theorem -> Obligations (Translate.translate_theorem lookups source ~path:key.path)
        | Function | Method -> (
            let prove_with substitution =
              Translate.translate_function
                ~is_updating_helper:(Contracts.is_updating_helper lookups key.path)
                ?inherited:(find_inherited_part lookups key.path)
                ~substitution lookups source ~path:key.path
            in
            match list_integer_instances lookups key.path with
            | [] -> Obligations (prove_with [])
            | instances ->
                let outcomes =
                  List.map
                    (fun (shown, substitution) ->
                      let outcome = prove_with substitution in
                      let prefix = "Where " ^ String.concat " and " shown ^ ": " in
                      {
                        outcome with
                        State.obligations =
                          List.map
                            (fun (obligation : State.obligation) ->
                              { obligation with message = Text prefix :: obligation.message })
                            outcome.obligations;
                      })
                    instances
                in
                Obligations
                  {
                    obligations =
                      List.concat_map
                        (fun (outcome : State.outcome) -> outcome.obligations)
                        outcomes;
                    holes =
                      List.sort_uniq compare
                        (List.concat_map (fun (outcome : State.outcome) -> outcome.holes) outcomes);
                  })
        | Test -> Obligations (Translate.test lookups source ~path:key.path)
        | Constant -> Obligations (Translate.translate_constant lookups source ~path:key.path)
        | Impl ->
            let outcomes = translate_impl_laws lookups key source in
            Obligations
              {
                obligations =
                  List.concat_map (fun (outcome : State.outcome) -> outcome.obligations) outcomes;
                holes = List.concat_map (fun (outcome : State.outcome) -> outcome.holes) outcomes;
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
      with
      | Facts.Unsupported (span, message) -> Unsupported (span, message)
      | Facts.Foreign_unsupported message -> Unsupported (Whole_definition, message))

let show_float bits =
  let shortest ~most ~same value =
    let rec shortest_digits digits =
      let text = Printf.sprintf "%.*g" digits value in
      if digits >= most || same (float_of_string text) then text else shortest_digits (digits + 1)
    in
    shortest_digits 1
  in
  let text =
    match String.length bits with
    | 64 ->
        let value = Int64.float_of_bits (Int64.of_string ("0b" ^ bits)) in
        shortest ~most:17 ~same:(fun read -> read = value) value
    | 32 ->
        let value = Int32.float_of_bits (Int32.of_string ("0b" ^ bits)) in
        shortest ~most:9
          ~same:(fun read -> Int32.bits_of_float read = Int32.bits_of_float value)
          value
    | _ -> "a float"
  in
  if text = "nan" || text = "-nan" then "NaN"
  else if text = "inf" then "infinity"
  else if text = "-inf" then "-infinity"
  else
    match String.index_opt text 'e' with
    | _ when String.contains text '.' -> text
    | Some at -> String.sub text 0 at ^ ".0" ^ String.sub text at (String.length text - at)
    | None -> text ^ ".0"

let show_truss_value members text =
  let tokens =
    let buffer = Buffer.create 16 and tokens = ref [] in
    let flush () =
      if Buffer.length buffer > 0 then begin
        tokens := `Atom (Buffer.contents buffer) :: !tokens;
        Buffer.clear buffer
      end
    in
    String.iter
      (function
        | '(' ->
            flush ();
            tokens := `Open :: !tokens
        | ')' ->
            flush ();
            tokens := `Close :: !tokens
        | ' ' | '\n' | '\t' | '\r' -> flush ()
        | character -> Buffer.add_char buffer character)
      text;
    flush ();
    List.rev !tokens
  in
  let constructor : Logic.symbol -> string = function
    | Constructor { variant = Some variant; _ } -> variant
    | Constructor { type_ = Named { path = Top { name; _ }; _ }; variant = None } -> name
    | Constructor { type_; variant = None } -> Types.show type_
    | other -> Logic.show_symbol other
  in
  let field : Logic.symbol -> string = function
    | Field { field; _ } -> field
    | other -> Logic.show_symbol other
  in
  let opaque atom = match String.index_opt atom '!' with Some _ -> true | None -> false in
  let bits atom =
    if String.length atom > 2 && String.sub atom 0 2 = "#b" then
      Some (String.sub atom 2 (String.length atom - 2))
    else if String.length atom > 2 && String.sub atom 0 2 = "#x" then
      Some
        (String.concat ""
           (List.map
              (fun digit ->
                let value = int_of_string ("0x" ^ String.make 1 digit) in
                String.init 4 (fun index -> if value land (8 lsr index) <> 0 then '1' else '0'))
              (List.of_seq (String.to_seq (String.sub atom 2 (String.length atom - 2))))))
    else None
  in
  let rec one = function
    | `Open :: `Atom "fp" :: `Atom sign :: `Atom exponent :: `Atom fraction :: `Close :: rest -> (
        match (bits sign, bits exponent, bits fraction) with
        | Some sign, Some exponent, Some fraction -> (show_float (sign ^ exponent ^ fraction), rest)
        | _ -> ("a float", rest))
    | `Open :: `Atom "_" :: `Atom special :: `Atom _ :: `Atom _ :: `Close :: rest ->
        ( (match special with
          | "+zero" -> "0.0"
          | "-zero" -> "-0.0"
          | "+oo" -> "infinity"
          | "-oo" -> "-infinity"
          | _ -> "NaN"),
          rest )
    | `Atom atom :: rest when opaque atom -> ("a value the prover knows nothing more about", rest)
    | `Atom atom :: rest -> (
        match List.assoc_opt atom members with
        | Some (internal, _) -> (constructor internal, rest)
        | None -> (atom, rest))
    | `Open :: `Atom "-" :: `Atom number :: `Close :: rest -> ("-" ^ number, rest)
    | `Open :: `Atom head :: rest ->
        let rec arguments acc = function
          | `Close :: rest -> (List.rev acc, rest)
          | [] -> (List.rev acc, [])
          | tokens ->
              let argument, rest = one tokens in
              arguments (argument :: acc) rest
        in
        let items, rest = arguments [] rest in
        let shown =
          match List.assoc_opt head members with
          | Some (internal, fields) when List.length fields = List.length items ->
              constructor internal ^ "("
              ^ String.concat ", "
                  (List.map2 (fun selector item -> field selector ^ ": " ^ item) fields items)
              ^ ")"
          | Some (internal, _) -> constructor internal ^ "(" ^ String.concat ", " items ^ ")"
          | None -> head ^ "(" ^ String.concat ", " items ^ ")"
        in
        (shown, rest)
    | `Open :: rest -> one rest
    | `Close :: rest -> one rest
    | [] -> ("", [])
  in
  fst (one tokens)

let show_counterexample members (obligation : State.obligation) answer_values =
  let shown =
    List.filter_map
      (fun (symbol, name) ->
        Option.map
          (fun value -> Printf.sprintf "`%s` is %s" name (show_truss_value members value))
          (List.assoc_opt symbol answer_values))
      (List.rev obligation.values @ List.rev obligation.locals)
  in
  let path =
    List.filter_map Fun.id
      (List.mapi
         (fun index (holding, failing, _, _) ->
           match
             ( List.assoc_opt (Logic.Symbol.Reached index) answer_values,
               List.assoc_opt (Logic.Symbol.Condition index) answer_values )
           with
           | Some "true", Some "true" -> Some holding
           | Some "true", Some "false" -> failing
           | _ -> None)
         obligation.decisions)
  in
  (match shown with [] -> "" | shown -> " For example, when " ^ String.concat ", " shown ^ ".")
  ^ match path with [] -> "" | path -> " On that path, " ^ String.concat ", " path ^ "."

let make_diagnostic code span message =
  Diagnostic.make ~code:(Diagnostic.Code.Prover code) span message

let resolve_location (names : Resolve.Names.lookups) (key : Resolve.Names.key)
    (location : State.location) =
  Source.Definition_span.locate (names.spans key)
    (match location with Node origin -> origin | Whole_definition -> (names.definition key).id)

let substitute_clause text spans clause replacements =
  let clause_span = Source.Definition_span.locate spans clause in
  let clause_text = Facts.quote_span text clause_span in
  let buffer = Buffer.create (String.length clause_text) in
  let next =
    List.fold_left
      (fun next ((span : Source.Definition_span.t), replacement) ->
        let start = span.start - clause_span.start and stop = span.stop - clause_span.start in
        if start < next || stop > String.length clause_text then next
        else begin
          Buffer.add_string buffer (String.sub clause_text next (start - next));
          Buffer.add_string buffer replacement;
          stop
        end)
      0
      (List.sort_uniq compare
         (List.map
            (fun (origin, replacement) -> (Source.Definition_span.locate spans origin, replacement))
            replacements))
  in
  Buffer.add_string buffer (String.sub clause_text next (String.length clause_text - next));
  Buffer.contents buffer

let render (lookups : Lookups.t) (message : State.message) =
  String.concat ""
    (List.map
       (function
         | State.Text text -> text
         | Quote (key, origin) ->
             Facts.quote_span
               (lookups.interface.names.text key)
               (Source.Definition_span.locate (lookups.interface.names.spans key) origin)
         | Substituted { key; clause; replacements } ->
             substitute_clause
               (lookups.interface.names.text key)
               (lookups.interface.names.spans key)
               clause replacements)
       message)

let render_fix lookups ({ title; edits } : State.fix) =
  Diagnostic.fix (render lookups title)
    (List.map
       (fun ({ at; replacement } : State.edit) ->
         Diagnostic.replace at (render lookups replacement))
       edits)

let locate_citation (lookups : Lookups.t) ((key : Resolve.Names.key), origin) =
  let place = lookups.interface.names.place key in
  ( place,
    Source.Definition_span.to_file ~base:place.base
      (Source.Definition_span.locate (lookups.interface.names.spans key) origin) )

type answer = Solved of Solver.answer | Ran of bool | Run_failed of string

type 'span state = {
  code : Diagnostic.Code.prover;
  span : 'span;
  shows : string;
  failure : 'span Diagnostic.diagnostic option;
  trusts_compiled_code : bool;
}

type verdict = (Source.Definition_span.t state * (Resolve.Names.key * Core.origin) option) list

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
        (fun (obligation : State.obligation) answer ->
          let span = resolve obligation.location in
          let message = render lookups obligation.message in
          let others =
            match obligation.code with
            | Overflow | Division | Shift ->
                " It can also be checked first with an `if`, done with the checked operation, or \
                 allowed to stop the program with `uses Panic`."
            | _ -> ""
          in
          let failed explained =
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
                | Ran false -> failed " Running it on this template's text gives `false`."
                | Run_failed report ->
                    failed
                      (" Running it on this template's text failed, so it is not known: " ^ report)
                | Solved (Counterexample values) ->
                    failed
                      (show_counterexample (Logic.list_members obligation.query) obligation values)
                | Solved Out_of_steps ->
                    failed
                      (" The solver ran out of steps, so it may hold but needs help: a `proof` \
                        block or a theorem."
                      ^
                      if Logic.has_untriggered_fact obligation.query then
                        " A quantified fact it may need has no term for the solver to use it by, \
                         so an `assert` that names the term it is needed for may be enough."
                      else ""));
              trusts_compiled_code = (match answer with Ran true -> true | _ -> false);
            },
            obligation.cited ))
        outcome.obligations answers

let request ~with_locals (obligation : State.obligation) =
  let symbols =
    List.map fst obligation.values @ if with_locals then List.map fst obligation.locals else []
  in
  let terms =
    if with_locals then
      List.concat
        (List.mapi
           (fun index (_, _, reached, condition) ->
             [ (Logic.Symbol.Reached index, reached); (Logic.Symbol.Condition index, condition) ])
           obligation.decisions)
    else []
  in
  (Solver.request ~symbols ~terms obligation.query, obligation.query)

let solve solver requests =
  let distinct = Hashtbl.create 64 in
  List.iter
    (fun ((request, _) as asked) ->
      if not (Hashtbl.mem distinct (Solver.request_key request)) then
        Hashtbl.replace distinct (Solver.request_key request) asked)
    requests;
  let distinct_requests =
    Hashtbl.fold (fun _ asked distinct_requests -> asked :: distinct_requests) distinct []
  in
  let answers = Hashtbl.create (List.length distinct_requests) in
  List.iter2
    (fun (request, _) canonical ->
      Hashtbl.replace answers (Solver.request_key request) (Solver.read request canonical))
    distinct_requests
    (Solver.solve_all solver distinct_requests);
  fun request -> Hashtbl.find answers (Solver.request_key request)

type question = Decided of answer | Asked of (Solver.request * Logic.query)

let run_answer runs ({ check; clause } : State.template_clause) =
  Option.map
    (function
      | Ok holds -> Ran (List.assoc clause (List.combine check.clauses holds))
      | Error report -> Run_failed report)
    (Template_check_table.find_opt runs check)

type verdicts = { lookups : Lookups.t; verdicts : verdict Key_table.t }

let decide ~runs lookups solver proofs =
  let runs = Template_check_table.of_seq (List.to_seq runs) in
  let question (obligation : State.obligation) =
    match Option.bind obligation.template_clause (run_answer runs) with
    | Some answer -> Decided answer
    | None -> Asked (request ~with_locals:false obligation)
  in
  let questions =
    List.map
      (fun (key, proof) ->
        let obligations =
          match proof with
          | Obligations (outcome : State.outcome) -> outcome.obligations
          | Unsupported _ | Not_proven_here -> []
        in
        (key, proof, List.map (fun obligation -> (obligation, question obligation)) obligations))
      proofs
  in
  let plain_answer =
    solve solver
      (List.concat_map
         (fun (_, _, questions) ->
           List.filter_map
             (function _, Asked asked -> Some asked | _, Decided _ -> None)
             questions)
         questions)
  in
  let local_questions =
    List.map
      (fun (key, proof, questions) ->
        ( key,
          proof,
          List.map
            (fun ((obligation : State.obligation), question) ->
              let local_request =
                match question with
                | Asked (plain_request, _)
                  when (obligation.locals <> [] || obligation.decisions <> [])
                       &&
                       match plain_answer plain_request with
                       | Counterexample _ -> true
                       | Proven | Out_of_steps -> false ->
                    Some (request ~with_locals:true obligation)
                | Asked _ | Decided _ -> None
              in
              (question, local_request))
            questions ))
      questions
  in
  let local_answer =
    solve solver
      (List.concat_map (fun (_, _, questions) -> List.filter_map snd questions) local_questions)
  in
  let verdicts = Key_table.create (List.length proofs) in
  List.iter
    (fun (key, proof, questions) ->
      let answers =
        List.map
          (fun (question, local_request) ->
            match (question, local_request) with
            | Decided answer, _ -> answer
            | Asked (plain_request, _), None -> Solved (plain_answer plain_request)
            | Asked (plain_request, _), Some (local_request, _) -> (
                match local_answer local_request with
                | Counterexample _ as answer -> Solved answer
                | Proven | Out_of_steps -> Solved (plain_answer plain_request)))
          questions
      in
      Key_table.replace verdicts key (list_definition_states lookups key proof answers))
    local_questions;
  { lookups; verdicts }

let file_states { lookups; verdicts } file =
  let verdict key = Option.value (Key_table.find_opt verdicts key) ~default:[] in
  List.map
    (fun declaration ->
      let key = Resolve.Names.make_key declaration in
      let ({ base; _ } : Resolve.Names.place) = lookups.interface.names.place key in
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
                match lookups.source place.file with
                | source ->
                    let line, _ = Source.position source span.start in
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
        (verdict key))
    (lookups.interface.names.declarations_in file)

let sort_diagnostics list =
  List.sort
    (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare (left.span, left.code) (right.span, right.code))
    list

let list_states verdicts file =
  List.concat (file_states verdicts file)
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
    (file_states verdicts file)
  |> sort_diagnostics
