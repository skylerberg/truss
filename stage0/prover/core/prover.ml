(* The prover's entry point. *)

open Syntax
module Translate = Translate
module Names = Resolve.Names
module Symbol = Logic.Symbol

type proof = Obligations of Translate.outcome | Unsupported of span * string | Not_proven_here

(* The trait's clauses an [impl]'s method keeps, with the [impl]'s type as
   [Self] and its arguments for the trait's parameters, and the body the
   trait provides for the method, if any. *)
let inherited database (path : Path.t) =
  match path with
  | Method { owner = impl; name; receiver } -> (
      match Query.demand database Interface.Environment.interface impl with
      | Some (Interface.Environment.Impl_interface interface) -> (
          let implemented = interface.implements.trait in
          let substitution =
            Option.value ~default:[] (Interface.Impls.trait_substitution database impl)
          in
          match Translate.trait_part database implemented name receiver with
          | Some part ->
              Some (part, substitution, Translate.provided_body database implemented name receiver)
          | None ->
              (* A capability's method takes no [self], so it is found with no
                 receiver. *)
              Option.map
                (fun part -> (part, substitution, None))
                (Translate.capability_part database implemented name))
      | _ -> None)
  | _ -> None

(* An [impl]'s obligation to keep each law of its trait. *)
let impl_laws database (key : Names.key) source =
  match Query.demand database Interface.Environment.interface key.path with
  | Some (Interface.Environment.Impl_interface interface)
    when not (Translate.impl_unfinished database key) ->
      [
        Translate.laws database source ~impl:key.path ~trait:interface.implements
          ~for_type:interface.for_type
          ~proofs:
            (Translate.law_proofs database (Path.package key.path) interface.implements
               interface.for_type)
          ~at:(Translate.definition_span source);
      ]
  | _ -> []

(* [standard::specification]'s contracts define the mathematical
   collections, so they are the trusted base, not obligations. *)
let is_specification_module (key : Names.key) = key.module_ = Well_known.specification

let declaration database (key : Names.key) =
  Names.Declaration_map.find_opt (key.path, key.ordinal)
    (Query.demand database Names.declaration_index key.module_)

(* The built-in types a type parameter can be, when one of its bounds is an
   integer trait. Only the built-in integer types implement those traits,
   so a definition generic over one is proven once for each type. *)
let integer_implementors (bounds : Types.trait_reference list) =
  let signed = Intrinsic.[ Int8; Int16; Int32; Int64; ISize ]
  and unsigned = Intrinsic.[ UInt8; UInt16; UInt32; UInt64; USize ] in
  List.fold_left
    (fun found (bound : Types.trait_reference) ->
      let these =
        if Well_known.is Signed_integer bound.trait then Some signed
        else if Well_known.is Unsigned_integer bound.trait then Some unsigned
        else if Well_known.is Fixed_width_integer bound.trait then Some (signed @ unsigned)
        else None
      in
      match (found, these) with
      | Some found, Some these -> Some (List.filter (fun builtin -> List.mem builtin these) found)
      | None, these | these, None -> these)
    None bounds

(* Each assignment of built-in types to a definition's type parameters that
   integer traits bound, with its description, as in [`Number` is `Int8`].
   A provided method of an integer trait has [Self] among them. *)
let integer_instances database (path : Path.t) =
  let generics =
    match Interface.Impls.signature database path with
    | Some signature ->
        List.filter_map
          (fun (generic : Types.generic) ->
            match generic.kind with
            | Type_generic bounds -> Some (generic.generic, bounds)
            | Value_generic | Capability_generic -> None)
          signature.generics
    | None -> []
  in
  let self =
    match path with
    | Method { owner; _ } ->
        [
          ( { Types.owner; name = "Self" },
            [ { Types.trait = owner; trait_arguments = []; associated = [] } ] );
        ]
    | _ -> []
  in
  List.fold_left
    (fun instances ((parameter : Types.parameter), bounds) ->
      match integer_implementors bounds with
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
                    (parameter, Types.Type (Types.builtin builtin)) :: substitution ))
                builtins)
            instances)
    [ ([], []) ]
    (self @ generics)
  |> List.filter (fun (shown, _) -> shown <> [])

let prove database (key : Names.key) =
  match (declaration database key, Translate.source_at_key database key) with
  | _ when is_specification_module key -> Not_proven_here
  | Some declaration, Some source -> (
      try
        match (declaration.kind, source.core.definition) with
        | (Function | Method), Function { body = None; _ } -> Not_proven_here
        | Theorem, Function _ -> Obligations (Translate.theorem database source ~path:key.path)
        | (Function | Method), Function { body = Some _; _ } -> (
            let prove_with substitution =
              Translate.function_
                ~updating_helper:(Translate.is_updating_helper database key.path)
                ?inherited:(inherited database key.path) ~substitution database source
                ~path:key.path
            in
            match integer_instances database key.path with
            | [] -> Obligations (prove_with [])
            | instances ->
                let outcomes =
                  List.map
                    (fun (shown, substitution) ->
                      let outcome = prove_with substitution in
                      let prefix = "Where " ^ String.concat " and " shown ^ ": " in
                      {
                        outcome with
                        Translate.obligations =
                          List.map
                            (fun (obligation : Translate.obligation) ->
                              { obligation with message = prefix ^ obligation.message })
                            outcome.obligations;
                      })
                    instances
                in
                Obligations
                  {
                    obligations =
                      List.concat_map
                        (fun (outcome : Translate.outcome) -> outcome.obligations)
                        outcomes;
                    holes =
                      List.sort_uniq compare
                        (List.concat_map
                           (fun (outcome : Translate.outcome) -> outcome.holes)
                           outcomes);
                  })
        | Test, Test _ -> Obligations (Translate.test database source ~path:key.path)
        | Constant, Constant _ -> Obligations (Translate.constant database source ~path:key.path)
        | Impl, _ ->
            let outcomes = impl_laws database key source in
            Obligations
              {
                obligations =
                  List.concat_map
                    (fun (outcome : Translate.outcome) -> outcome.obligations)
                    outcomes;
                holes =
                  List.concat_map (fun (outcome : Translate.outcome) -> outcome.holes) outcomes;
              }
        | Type, Type { invariants = _ :: _; _ } | Type, Type { potential = Some _; _ } ->
            Obligations (Translate.type_ database source ~path:key.path)
        | _ -> Not_proven_here
      with
      | Translate.Unsupported (span, message) -> Unsupported (span, message)
      | Translate.Foreign_unsupported message -> Unsupported (Syntax.Span.make 0 0, message))
  | _ -> Not_proven_here

let proof = Query.query ~phase:Phases.proofs ~name:"proof" ~show:Names.show_key prove

(* A value from the solver's model, written as Truss writes it: a negative
   number with its sign, and a datatype's value as its variant or record,
   with its fields in parentheses. *)
(* A float from the solver's model, as Truss writes it: the shortest
   decimal that reads back as the same bits, with a point. *)
let float_text bits =
  (* The fewest significant digits, up to [most], that read back as
     [value], by [same]. *)
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
    (* A Truss float has digits on both sides of its point. *)
    match String.index_opt text 'e' with
    | _ when String.contains text '.' -> text
    | Some at -> String.sub text 0 at ^ ".0" ^ String.sub text at (String.length text - at)
    | None -> text ^ ".0"

let truss_value members text =
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
  (* A constructor's name as Truss writes it: its variant, or for a record
     its type's own name. *)
  let constructor : Logic.symbol -> string = function
    | Constructor { variant = Some variant; _ } -> variant
    | Constructor { type_name; variant = None; _ } -> type_name
    | other -> Logic.show_symbol other
  in
  let field : Logic.symbol -> string = function
    | Field { field; _ } -> field
    | other -> Logic.show_symbol other
  in
  let opaque atom =
    (* The solver's name for a value of a sort it knows nothing about. *)
    match String.index_opt atom '!' with
    | Some _ -> true
    | None -> false
  in
  (* A bit-vector the solver writes in binary, [#b...], or in hex, [#x...]. *)
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
        | Some sign, Some exponent, Some fraction -> (float_text (sign ^ exponent ^ fraction), rest)
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

(* The parameters' values, in order, then the locals'. *)
let counterexample members (obligation : Translate.obligation) answer_values =
  let shown =
    List.filter_map
      (fun (symbol, name) ->
        Option.map
          (fun value -> Printf.sprintf "`%s` is %s" name (truss_value members value))
          (List.assoc_opt symbol answer_values))
      (List.rev obligation.values @ List.rev obligation.locals)
  in
  (* Each [if] the path reaches, by whether its condition holds there, and
     each arm of a [match] it takes. *)
  let path =
    List.filter_map Fun.id
      (List.mapi
         (fun index (holding, failing, _, _) ->
           match
             ( List.assoc_opt (Symbol.Reached index) answer_values,
               List.assoc_opt (Symbol.Condition index) answer_values )
           with
           | Some "true", Some "true" -> Some holding
           | Some "true", Some "false" -> failing
           | _ -> None)
         obligation.decisions)
  in
  (match shown with [] -> "" | shown -> " For example, when " ^ String.concat ", " shown ^ ".")
  ^ match path with [] -> "" | path -> " On that path, " ^ String.concat ", " path ^ "."

let diagnostic code span message = Diagnostic.make ~code:(Diagnostic.Code.Prover code) span message

(* A span inside its definition's text, which every span of the
   definition's own tree is; anything else would be a bug, and is shown at
   the definition's start rather than outside its file. *)
let clamp_to_definition database (key : Names.key) (span : span) =
  match Query.demand database Names.text key with
  | Some text when span.stop <= String.length text -> span
  | _ -> Syntax.Span.make 0 0

(* An obligation's answer: the solver's, or the result of running the code
   that decides it, or that it timed out, or none yet, while a response it
   needs is pending. *)
type answer = Solved of Solver.answer | Ran_true | Ran_false | Run_timed_out | Pending_answer
type run = Template_check of Translate.evaluation | Call of Translate.known_call
type run_result = Returned of Z.t | Timed_out | Not_run

(* The caller gives the evaluator, since the prover does not depend on
   code generation. [code_key] changes exactly when a run's result may,
   and is [None] where the code cannot be built. *)
type evaluator = { code_key : run -> string option; run : run -> run_result }

let no_evaluator = { code_key = (fun _ -> None); run = (fun _ -> Not_run) }

type oracles = {
  solve : index:int -> with_locals:bool -> solver_response;
  check_template : Translate.evaluation -> run_result;
  call : Translate.known_call -> Z.t option;
}

(* The solver's response to one query: its answer, or none yet. *)
and solver_response = Answered of Solver.answer | Unanswered

(* The values of the calls a query mentions that running them gave, as
   facts, which are only as true as the compiled code, which the prover
   trusts. *)
let call_facts ~call (obligation : Translate.obligation) =
  List.filter_map
    (fun (known : Translate.known_call) ->
      Option.map
        (fun value ->
          Logic.equal known.term
            (if known.result_is_bool then Logic.Boolean (not (Z.equal value Z.zero))
             else Logic.Integer value))
        (call known))
    obligation.known_calls

(* An obligation's query, with the results of running its calls. The same
   query, not a copy, when nothing is added, so the solver finds its earlier
   answer. *)
let query_of ~call (obligation : Translate.obligation) =
  match call_facts ~call obligation with
  | [] -> obligation.query
  | added -> { obligation.query with facts = obligation.query.facts @ added }

let answers (oracles : oracles) (obligations : Translate.obligation list) =
  List.mapi
    (fun index (obligation : Translate.obligation) ->
      let answer =
        match Option.map oracles.check_template obligation.evaluation with
        | Some (Returned value) -> if Z.equal value Z.zero then Ran_false else Ran_true
        | Some Timed_out -> Run_timed_out
        | Some Not_run | None -> (
            match oracles.solve ~index ~with_locals:false with
            | Unanswered -> Pending_answer
            | Answered (Solver.Counterexample _ as plain)
              when obligation.locals <> [] || obligation.decisions <> [] -> (
                match oracles.solve ~index ~with_locals:true with
                | Answered (Solver.Counterexample _ as answer) -> Solved answer
                | Answered _ -> Solved plain
                | Unanswered -> Pending_answer)
            | Answered answer -> Solved answer)
      in
      (obligation, answer))
    obligations

type 'span state = {
  code : Diagnostic.Code.prover;
  span : 'span;
  shows : string;
  failure : 'span Diagnostic.diagnostic option;
  trusts_compiled_code : bool;
}

let definition_states oracles database (key : Names.key) =
  let clamp_to_definition span = clamp_to_definition database key span in
  match Query.demand database proof key with
  | Not_proven_here -> []
  | Unsupported (span, construct) ->
      let message =
        Printf.sprintf "The prover cannot read %s yet, so nothing in this definition is proven."
          construct
      in
      [
        ( {
            code = Unsupported;
            span = clamp_to_definition span;
            shows = message;
            failure = Some (diagnostic Unsupported (clamp_to_definition span) message);
            trusts_compiled_code = false;
          },
          None );
      ]
  | Obligations outcome ->
      List.map
        (fun ((obligation : Translate.obligation), (answer : answer)) ->
          let span = clamp_to_definition obligation.span in
          (* These fixes change the code's semantics, so they are named, not
             applied. *)
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
                (diagnostic obligation.code span (obligation.message ^ explained ^ others)) with
                fixes = obligation.fixes;
              }
          in
          ( {
              code = obligation.code;
              span;
              shows = obligation.message;
              failure =
                (match answer with
                | Solved Proven | Ran_true | Pending_answer -> None
                | Ran_false -> failed " Running it on this template's text gives `false`."
                | Run_timed_out ->
                    failed
                      " Running it on this template's text took longer than the time limit, so it \
                       is not known."
                | Solved (Counterexample values) ->
                    failed (counterexample (Logic.members obligation.query) obligation values)
                | Solved Out_of_steps ->
                    failed
                      (" The solver ran out of steps, so it may hold but needs help: a `proof` \
                        block or a theorem."
                      ^
                      if Logic.untriggered obligation.query then
                        " A quantified fact it may need has no term for the solver to use it by, \
                         so an `assert` that names the term it is needed for may be enough."
                      else ""));
              trusts_compiled_code =
                (match answer with
                | Ran_true -> true
                | Solved Proven -> call_facts ~call:oracles.call obligation <> []
                | _ -> false);
            },
            obligation.cited ))
        (answers oracles outcome.obligations)

(* One query an obligation may ask: the obligation's index, and whether a
   counterexample gives the locals too. *)
type question = { definition : Names.key; index : int; with_locals : bool }

let show_question question =
  Printf.sprintf "%s #%d" (Names.show_key question.definition) question.index

(* A request to an oracle, and the oracle's response, kept by the
   request's key. A solver's request holds no query text, so it carries
   its question, from which the query is derived again to be run. A run's
   response holds the key of the code that ran, so the driver can tell
   when the code has changed since. *)
type oracle_request = Solve of question * Solver.request | Run of run

type oracle_response =
  | Solver_response of Solver.canonical
  | Run_response of { code_key : string option; result : run_result }

let request_key = function
  | Solve (_, request) -> "solve " ^ Solver.request_key request
  | Run (Template_check evaluation) ->
      "template " ^ Digest.to_hex (Digest.string (Marshal.to_string evaluation []))
  | Run (Call call) -> "call " ^ Digest.to_hex (Digest.string (Marshal.to_string call []))

let oracle_response : (string, oracle_response) Query.input =
  Query.input ~name:"oracle_response" ~show:Fun.id ()

(* A definition's outcome: its states, once every response they need is
   recorded, or the requests still pending. *)
type outcome =
  | Decided of (span state * (Names.key * Syntax.span) option) list
  | Pending of oracle_request list

let run_result database run =
  match Query.find database oracle_response (request_key (Run run)) with
  | Some (Run_response response) -> Some response.result
  | Some (Solver_response _) | None -> None

let call_value database call =
  match run_result database (Call call) with Some (Returned value) -> Some value | _ -> None

let runs =
  Query.query ~name:"proof_runs" ~phase:Phases.verdicts ~saved:true ~show:Names.show_key
    (fun database key ->
      match Query.demand database proof key with
      | Obligations outcome ->
          List.sort_uniq compare
            (List.concat_map
               (fun (obligation : Translate.obligation) ->
                 Option.to_list
                   (Option.map (fun evaluation -> Template_check evaluation) obligation.evaluation)
                 @ List.map (fun call -> Call call) obligation.known_calls)
               outcome.obligations)
      | Not_proven_here | Unsupported _ -> [])

(* The query a question asks, with the symbols and the named terms whose
   values a counterexample should give. *)
let question_query database question =
  match Query.demand database proof question.definition with
  | Obligations outcome -> (
      match List.nth_opt outcome.obligations question.index with
      | Some obligation ->
          let values =
            List.map fst obligation.values
            @ if question.with_locals then List.map fst obligation.locals else []
          in
          let terms =
            if question.with_locals then
              List.concat
                (List.mapi
                   (fun index (_, _, reached, condition) ->
                     [ (Symbol.Reached index, reached); (Symbol.Condition index, condition) ])
                   obligation.decisions)
            else []
          in
          Some (query_of ~call:(call_value database) obligation, values, terms)
      | None -> None)
  | Not_proven_here | Unsupported _ -> None

let question_request =
  Query.query ~name:"question_request" ~phase:Phases.verdicts ~saved:true ~show:show_question
    (fun database question ->
      Option.map
        (fun (query, values, terms) -> Solver.request ~values ~terms query)
        (question_query database question))

let outcome =
  Query.query ~name:"proof_outcome" ~phase:Phases.verdicts ~saved:true ~show:Names.show_key
    (fun database key ->
      match
        List.filter (fun run -> run_result database run = None) (Query.demand database runs key)
      with
      | _ :: _ as pending -> Pending (List.map (fun run -> Run run) pending)
      | [] -> (
          let pending = ref [] in
          let oracles =
            {
              solve =
                (fun ~index ~with_locals ->
                  let question = { definition = key; index; with_locals } in
                  match Query.demand database question_request question with
                  | None -> Answered Out_of_steps
                  | Some request -> (
                      let oracle_request = Solve (question, request) in
                      match Query.find database oracle_response (request_key oracle_request) with
                      | Some (Solver_response canonical) -> Answered (Solver.read request canonical)
                      | Some (Run_response _) | None ->
                          if not (List.mem oracle_request !pending) then
                            pending := oracle_request :: !pending;
                          Unanswered));
              check_template =
                (fun evaluation ->
                  Option.value (run_result database (Template_check evaluation)) ~default:Not_run);
              call = call_value database;
            }
          in
          let states = definition_states oracles database key in
          match !pending with [] -> Decided states | pending -> Pending (List.rev pending)))

(* A run's response: its result, under the key of the code that ran. *)
let run_response (evaluator : evaluator) run code_key =
  Run_response
    { code_key; result = (match code_key with None -> Not_run | Some _ -> evaluator.run run) }

(* The oracles' responses to the requests, by request key: the solver's,
   several at once, and the evaluator's. The driver records them, so its
   database can save them with its state. *)
let responses (evaluator : evaluator) database solver requests =
  (* Questions of different definitions can ask the same query, which is
     run once. *)
  let distinct_requests = Hashtbl.create 64 in
  List.iter
    (function
      | Solve (question, request)
        when not (Hashtbl.mem distinct_requests (Solver.request_key request)) ->
          Hashtbl.replace distinct_requests (Solver.request_key request) (question, request)
      | Solve _ | Run _ -> ())
    requests;
  let solver_requests =
    Hashtbl.fold
      (fun _ (question, request) solver_requests ->
        match question_query database question with
        | Some (query, _, _) -> (request, query) :: solver_requests
        | None -> Compiler_bug.bug ~stage:"Prover" "a pending question asks no query")
      distinct_requests []
  in
  let answers = Hashtbl.create (List.length solver_requests) in
  List.iter2
    (fun (request, _) answer -> Hashtbl.replace answers (Solver.request_key request) answer)
    solver_requests
    (Solver.solve_all solver solver_requests);
  List.map
    (fun request ->
      ( request_key request,
        match request with
        | Solve (_, solver_request) ->
            Solver_response (Hashtbl.find answers (Solver.request_key solver_request))
        | Run run -> run_response evaluator run (evaluator.code_key run) ))
    requests

(* The responses of the definitions' runs whose code has changed since they
   ran, or that timed out, run again. The code a run reaches is not among
   an outcome's reads, so without this a callee's new body would leave its
   callers proven by its old result. A timeout is not kept, as code
   generation keeps no failed run, since the same run can finish on a less
   loaded machine. *)
let rerun_changed (evaluator : evaluator) database keys =
  List.sort_uniq compare (List.concat_map (Query.demand database runs) keys)
  |> List.filter_map (fun run ->
      let code_key = evaluator.code_key run in
      match Query.find database oracle_response (request_key (Run run)) with
      | Some (Run_response recorded)
        when recorded.code_key = code_key && recorded.result <> Timed_out ->
          None
      | Some _ | None -> Some (request_key (Run run), run_response evaluator run code_key))

let solve_ahead ?(evaluator = no_evaluator) ~record database solver files =
  let keys =
    List.concat_map
      (fun file ->
        List.filter_map
          (fun declaration ->
            let key = Names.key_of declaration in
            match Query.demand database Names.base key with Some _ -> Some key | None -> None)
          (Query.demand database Names.declarations_in file))
      files
  in
  (match rerun_changed evaluator database keys with [] -> () | changed -> record changed);
  let rec round keys =
    let pending =
      List.filter_map
        (fun key ->
          match Query.demand database outcome key with
          | Decided _ -> None
          | Pending requests -> Some (key, requests))
        keys
    in
    if pending <> [] then begin
      record
        (responses evaluator database solver (List.sort_uniq compare (List.concat_map snd pending)));
      round (List.map fst pending)
    end
  in
  round keys

let decided database key =
  match Query.demand database outcome key with
  | Decided states -> states
  | Pending _ -> Compiler_bug.bug ~stage:"Prover" "an outcome is still pending once decided"

(* Each definition's states, in the file's offsets. A failure of a clause
   that another definition of the file states has a note at that clause. *)
let file_states ?evaluator ~record database solver file =
  solve_ahead ?evaluator ~record database solver [ file ];
  List.filter_map
    (fun declaration ->
      let key = Names.key_of declaration in
      let base_of key = Query.demand database Names.base key in
      match base_of key with
      | Some (_, base) ->
          Some
            (List.map
               (fun (state, cited) ->
                 let note =
                   match cited with
                   | Some (cited, span) -> (
                       match base_of cited with
                       | Some (cited_file, offset) when cited_file = file ->
                           Some
                             ( Span.to_source ~base:offset (clamp_to_definition database cited span),
                               "This is the clause that must hold." )
                       | _ -> None)
                   | _ -> None
                 in
                 (* A clause in another file is named by where it is, since a
                    note is in the diagnostic's own file. *)
                 let elsewhere =
                   match cited with
                   | Some (cited, span) -> (
                       match base_of cited with
                       | Some (cited_file, offset) when cited_file <> file -> (
                           match Query.demand database Packages.source cited_file with
                           | source ->
                               let start =
                                 (Span.to_source ~base:offset
                                    (clamp_to_definition database cited span))
                                   .start
                               in
                               let line, _ = Source.position source start in
                               Printf.sprintf " The clause that must hold is at `%s:%d`."
                                 (Source.path source) line
                           | exception Not_found -> "")
                       | _ -> "")
                   | _ -> ""
                 in
                 {
                   state with
                   span = Span.to_source ~base state.span;
                   failure =
                     Option.map
                       (fun failure ->
                         let failure = Diagnostic.map_spans (Span.to_source ~base) failure in
                         let failure = { failure with message = failure.message ^ elsewhere } in
                         match note with
                         | Some note -> { failure with notes = failure.notes @ [ note ] }
                         | None -> failure)
                       state.failure;
                 })
               (decided database key))
      | None -> None)
    (Query.demand database Names.declarations_in file)

let sorted_diagnostics list =
  List.sort
    (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare (left.span, left.code) (right.span, right.code))
    list

let states ?evaluator ~record database solver file =
  List.concat (file_states ?evaluator ~record database solver file)
  |> List.sort (fun left right -> compare (left.span, left.code) (right.span, right.code))

let diagnostics ?evaluator ~record database solver file =
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
    (file_states ?evaluator ~record database solver file)
  |> sorted_diagnostics
