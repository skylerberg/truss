(* The prover's entry point. *)

open Syntax
module Translate = Translate
module Names = Resolve.Names
module L = Logic
module S = Logic.Symbol

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
let impl_laws ?reveal database (key : Names.key) source =
  match Query.demand database Interface.Environment.interface key.path with
  | Some (Interface.Environment.Impl_interface interface)
    when not (Translate.impl_unfinished database key) ->
      [
        Translate.laws ?reveal database source ~impl:key.path ~trait:interface.implements
          ~for_type:interface.for_type
          ~proofs:
            (Translate.law_proofs database (Path.package key.path) interface.implements
               interface.for_type)
          ~at:(Translate.definition_span source);
      ]
  | _ -> []

(* [standard::specification]'s contracts say what the mathematical
   collections are, so they are the trusted base, not obligations. *)
let specification (key : Names.key) = key.module_ = Well_known.specification

let declaration database (key : Names.key) =
  Names.Declaration_map.find_opt (key.path, key.ordinal)
    (Query.demand database Names.declaration_index key.module_)

let prove ?reveal database (key : Names.key) =
  match (declaration database key, Translate.source_at_key database key) with
  | _ when specification key -> Not_proven_here
  | Some declaration, Some source -> (
      try
        match (declaration.kind, source.core.definition) with
        (* A trait's method without a body is only declared, and an [impl]
           shows it. A provided body is proven once, here, with [Self] the
           trait's type parameter, so it keeps the trait's clauses for every
           [impl] that keeps it. *)
        | (Function | Method), Function { body = None; _ } -> Not_proven_here
        | Theorem, Function _ ->
            Obligations (Translate.theorem ?reveal database source ~path:key.path)
        | (Function | Method), Function { body = Some _; _ } ->
            Obligations
              (Translate.function_ ?reveal
                 ~updating_helper:(Translate.is_updating_helper database key.path)
                 ?inherited:(inherited database key.path) database source ~path:key.path)
        | Test, Test _ -> Obligations (Translate.test ?reveal database source ~path:key.path)
        | Constant, Constant _ ->
            Obligations (Translate.constant ?reveal database source ~path:key.path)
        | Impl, _ ->
            let outcomes = impl_laws ?reveal database key source in
            Obligations
              {
                obligations =
                  List.concat_map (fun (o : Translate.outcome) -> o.obligations) outcomes;
                holes = List.concat_map (fun (o : Translate.outcome) -> o.holes) outcomes;
              }
        | Type, Type { invariants = _ :: _; _ } | Type, Type { potential = Some _; _ } ->
            Obligations (Translate.type_ ?reveal database source ~path:key.path)
        | _ -> Not_proven_here
      with
      | Translate.Unsupported (span, message) -> Unsupported (span, message)
      | Translate.Foreign_unsupported message -> Unsupported (Syntax.Span.make 0 0, message))
  | _ -> Not_proven_here

let proof = Query.query ~phase:Phases.proofs ~name:"proof" ~show:Names.show_key (prove ?reveal:None)

(* A definition's obligations with every callee read as its own package
   reads it, hidden bodies included, in the same order as its own: asked
   of only where one of them is not proven and names a hidden callee. *)
let revealed_proof =
  Query.query ~phase:Phases.proofs ~name:"revealed_proof" ~show:Names.show_key (prove ~reveal:true)

(* Messages *)

(* A value from the solver's model, written as Truss writes it: a negative
   number with its sign, and a datatype's value as its variant or record,
   with its fields in parentheses. *)
(* A float from the solver's model, as Truss writes it: the shortest
   decimal that reads back as the same bits, with a point. *)
let float_text bits =
  (* The fewest significant digits, up to [most], that read back as
     [value], by [same]. *)
  let shortest ~most ~same value =
    let rec go digits =
      let text = Printf.sprintf "%.*g" digits value in
      if digits >= most || same (float_of_string text) then text else go (digits + 1)
    in
    go 1
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
    let buffer = Buffer.create 16 and found = ref [] in
    let flush () =
      if Buffer.length buffer > 0 then begin
        found := `Atom (Buffer.contents buffer) :: !found;
        Buffer.clear buffer
      end
    in
    String.iter
      (function
        | '(' ->
            flush ();
            found := `Open :: !found
        | ')' ->
            flush ();
            found := `Close :: !found
        | ' ' | '\n' | '\t' | '\r' -> flush ()
        | c -> Buffer.add_char buffer c)
      text;
    flush ();
    List.rev !found
  in
  (* A constructor's name as Truss writes it: its variant, or for a record
     its type's own name. *)
  let constructor : S.t -> string = function
    | Constructor { variant = Some variant; _ } -> variant
    | Constructor { type_name; variant = None; _ } -> type_name
    | other -> S.show other
  in
  let field : S.t -> string = function Field { field; _ } -> field | other -> S.show other in
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
             ( List.assoc_opt (S.Reached index) answer_values,
               List.assoc_opt (S.Condition index) answer_values )
           with
           | Some "true", Some "true" -> Some holding
           | Some "true", Some "false" -> failing
           | _ -> None)
         obligation.decisions)
  in
  (match shown with [] -> "" | shown -> " For example, when " ^ String.concat ", " shown ^ ".")
  ^ match path with [] -> "" | path -> " On that path, " ^ String.concat ", " path ^ "."

let diagnostic code span message = Diagnostic.make ~code:(Diagnostic.Code.Prover code) span message
let source_span (span : span) : Diagnostic.span = Syntax.Span.to_source span

(* A span inside its definition's text, which every span of the
   definition's own tree is; anything else would be a bug, and is shown at
   the definition's start rather than outside its file. *)
let within database (key : Names.key) (span : span) =
  match Query.demand database Names.text key with
  | Some text when span.stop <= String.length text -> span
  | _ -> Syntax.Span.make 0 0

(* Bitwise operations, exactly. A query proves bitwise facts first from
   the few facts the prover states about [&], [|], [^], [~], and shifts;
   when it does not, and it mentions any, it is asked once more with each
   of them defined exactly, as the operation on its operands' bits of
   their type's width, which the solver decides by bit-blasting. A
   definition says what the operation is, so the second query means what
   the first does, and its answer is as sound. *)
(* An obligation's answer: the solver's, or what running the code that
   decides it gave, or that it timed out, or none yet, while a response it
   needs is pending. [Solved_hidden] is an answer that is not a proof,
   where the query with the definitions of the callees whose bodies are
   hidden here proves. *)
type answer =
  | Solved of Solver.answer
  | Solved_hidden of Solver.answer
  | Ran_true
  | Ran_false
  | Run_timed_out
  | Pending_answer

let proven = function Solved Proven | Ran_true -> true | _ -> false

(* A run of compiled code that decides part of a proof: a template's
   check, or a call whose arguments are known. *)
type run = Template_check of Translate.evaluation | Call of Translate.known_call

(* What a run gave: an integer, or a [Bool] as 0 or 1; that it timed out;
   or that it was not run, since its code cannot be built. *)
type run_result = Returned of Z.t | Timed_out | Not_run

(* The caller gives the evaluator, since the prover does not depend on
   code generation. [code_key] changes exactly when what a run gives may,
   and is [None] where the code cannot be built. *)
type evaluator = { code_key : run -> string option; run : run -> run_result }

let no_evaluator = { code_key = (fun _ -> None); run = (fun _ -> Not_run) }

let bitwise_operations =
  [
    "and";
    "or";
    "xor";
    "complement";
    "shift_left";
    "shift_right";
    "rotate_left";
    "rotate_right";
    "swap_bytes";
  ]

let bitwise_of : S.t -> _ = function
  | Opaque_operation { operation; integer = Some (bits, signed); _ }
    when List.mem operation bitwise_operations ->
      Some (operation, bits, signed)
  | _ -> None

let exactly (query : L.query) =
  let found = ref [] in
  let rec walk bound = function
    | L.Apply (name, arguments) as term ->
        (if bitwise_of name <> None && not (List.mem_assoc term !found) then
           let named = List.filter (fun (symbol, _) -> L.mentions [ symbol ] term) bound in
           found := (term, named) :: !found);
        List.iter (walk bound) arguments
    | L.Forall (symbols, body) | L.Exists (symbols, body) -> walk (symbols @ bound) body
    | term -> List.iter (walk bound) (L.arguments term)
  in
  List.iter (walk []) (query.goal :: query.facts);
  let definition term =
    match term with
    | L.Apply (name, arguments) -> (
        match (bitwise_of name, arguments) with
        | Some (operation, bits, signed), first :: rest ->
            let bits_of value = L.Operation (Printf.sprintf "(_ int2bv %d)" bits, [ value ]) in
            let a = bits_of first in
            let result =
              match (operation, rest) with
              | "complement", _ -> Some (L.Operation ("bvnot", [ a ]))
              | "and", [ b ] -> Some (L.Operation ("bvand", [ a; bits_of b ]))
              | "or", [ b ] -> Some (L.Operation ("bvor", [ a; bits_of b ]))
              | "xor", [ b ] -> Some (L.Operation ("bvxor", [ a; bits_of b ]))
              | "shift_left", [ b ] -> Some (L.Operation ("bvshl", [ a; bits_of b ]))
              | "shift_right", [ b ] ->
                  Some (L.Operation ((if signed then "bvashr" else "bvlshr"), [ a; bits_of b ]))
              | ("rotate_left" | "rotate_right"), [ b ] ->
                  (* By the amount modulo the width, with what leaves one end
                     coming in at the other. *)
                  let by = bits_of (L.Operation ("mod", [ b; L.int bits ])) in
                  let rest = L.Operation ("bvsub", [ bits_of (L.int bits); by ]) in
                  let towards, back =
                    if operation = "rotate_left" then ("bvshl", "bvlshr") else ("bvlshr", "bvshl")
                  in
                  Some
                    (L.Operation
                       ( "bvor",
                         [ L.Operation (towards, [ a; by ]); L.Operation (back, [ a; rest ]) ] ))
              | "swap_bytes", _ ->
                  let byte index =
                    L.Operation
                      (Printf.sprintf "(_ extract %d %d)" ((8 * index) + 7) (8 * index), [ a ])
                  in
                  let bytes = List.init (bits / 8) byte in
                  Some
                    (List.fold_left
                       (fun swapped next -> L.Operation ("concat", [ swapped; next ]))
                       (List.hd bytes) (List.tl bytes))
              | _ -> None
            in
            Option.map
              (fun result ->
                let unsigned = L.Operation ("bv2nat", [ result ]) in
                let value =
                  if signed then
                    let half = L.Integer (Z.shift_left Z.one (bits - 1)) in
                    L.ite
                      (L.Operation (">=", [ unsigned; half ]))
                      (L.Operation ("-", [ unsigned; L.Integer (Z.shift_left Z.one bits) ]))
                      unsigned
                  else unsigned
                in
                L.equal term value)
              result
        | _ -> None)
    | _ -> None
  in
  (* A term under a quantifier that names its bound symbols is defined for
     each of their values. *)
  let defined (term, named) =
    Option.map
      (fun definition -> if named = [] then definition else L.Forall (named, definition))
      (definition term)
  in
  match List.filter_map defined (List.rev !found) with
  | [] -> None
  | definitions -> Some { query with facts = query.facts @ definitions }

(* Which of an obligation's queries is asked: as it was made, or with its
   bitwise operations defined exactly, either of those without its
   callees' definitions, or with the definitions of the callees whose
   bodies are hidden here. *)
type variant = Made | Exact | Alone | Alone_exact | Revealed

(* The oracles a definition's proof is decided by: the solver, of one of
   its obligations' queries, by the obligation's index, the choice of
   constants for its bounds, the variant, and whether a counterexample
   gives the locals too; and the evaluator, of a template's check and of
   the values of the known calls. A definition's outcome is derived from
   their responses. *)
type oracles = {
  solve :
    index:int ->
    choice:(S.t * (Z.t * Z.t)) list ->
    variant:variant ->
    with_locals:bool ->
    solver_response;
  check_template : Translate.evaluation -> run_result;
  call : Translate.known_call -> Z.t option;
}

(* The solver's response to one query: its answer; none yet, so a search
   that would ask more after it stops there instead; or that the query does
   not exist. *)
and solver_response = Answered of Solver.answer | Unanswered | No_query

(* The values of the calls a query mentions that running them gave, as
   facts, which are only as true as the compiled code, which the prover
   trusts. *)
let given ~call (obligation : Translate.obligation) =
  List.filter_map
    (fun (known : Translate.known_call) ->
      Option.map
        (fun value ->
          L.equal known.term
            (if known.result_is_bool then L.Boolean (not (Z.equal value Z.zero))
             else L.Integer value))
        (call known))
    obligation.known_calls

(* An obligation's query, or another of its own, with a choice of
   constants for its bounds. *)
let query_with ?query ~call (obligation : Translate.obligation) choice =
  let query = Option.value query ~default:obligation.query in
  let pins =
    List.map
      (fun (constants : Costs.constants) ->
        Costs.pin constants (List.assoc constants.factor choice))
      obligation.constants
  in
  (* The same query, not a copy, when nothing is added, so the solver finds
     what it made of it before. *)
  match pins @ given ~call obligation with
  | [] -> query
  | added -> { query with facts = query.facts @ added }

(* Every choice of a pair of constants for each bound the obligations
   mention, in the order they are tried. *)
let choices (obligations : Translate.obligation list) =
  let groups =
    List.fold_left
      (fun groups (obligation : Translate.obligation) ->
        List.fold_left
          (fun groups (constants : Costs.constants) ->
            if List.exists (fun (g : Costs.constants) -> g.factor = constants.factor) groups then
              groups
            else groups @ [ constants ])
          groups obligation.constants)
      [] obligations
  in
  let rec all = function
    | [] -> [ [] ]
    | (constants : Costs.constants) :: rest ->
        List.concat_map
          (fun pair -> List.map (fun choice -> (constants.factor, pair) :: choice) (all rest))
          constants.pairs
  in
  all groups

(* An obligation's query of a variant, with a choice of constants, and
   with what running code gave of its calls. *)
let variant_query ~call (obligation : Translate.obligation) choice variant =
  let made base = query_with ?query:base ~call obligation choice in
  match variant with
  | Made -> Some (made None)
  | Exact -> exactly (made None)
  | Alone -> Option.map (fun query -> made (Some query)) obligation.contracts_alone
  | Alone_exact -> Option.bind obligation.contracts_alone (fun query -> exactly (made (Some query)))
  | Revealed -> Some (made None)

(* Each obligation's answer. One that mentions the constants of [O(...)]
   bounds is asked with each choice of a pair for every bound in turn, the
   same choice for all of them, since a recursive call assumes the bound
   with the constants it is shown with; the first choice that proves them
   all is taken, and if none does, the answers are the first choice's. *)
let answers (oracles : oracles) (obligations : Translate.obligation list) =
  let solve index (obligation : Translate.obligation) choice =
    (* A clause that running code decides is decided so, and the solver is
       never asked. *)
    match Option.map oracles.check_template obligation.evaluation with
    | Some (Returned value) -> if Z.equal value Z.zero then Ran_false else Ran_true
    | Some Timed_out -> Run_timed_out
    | Some Not_run | None -> (
        (* Each question is asked only once what it depends on is
           answered: a pending response stops the search, which goes on
           once it is answered, rather than asking what the answer may make
           unneeded. *)
        let ask variant ~with_locals = oracles.solve ~index ~choice ~variant ~with_locals in
        let asked made exact =
          match ask made ~with_locals:false with
          | Answered Solver.Proven -> Some Solver.Proven
          | Answered first -> (
              match ask exact ~with_locals:false with
              | Answered answer -> Some answer
              | Unanswered -> None
              | No_query -> Some first)
          | Unanswered -> None
          | No_query -> Some Solver.Out_of_steps
        in
        match (asked Made Exact, obligation.contracts_alone) with
        | None, _ -> Pending_answer
        | Some Solver.Out_of_steps, Some _ -> (
            (* Without its callees' definitions, a query is about their
               contracts alone, which can be enough where unfolding is too
               much for the solver. *)
            match asked Alone Alone_exact with
            | None -> Pending_answer
            | Some Solver.Proven -> Solved Proven
            | Some _ -> Solved Out_of_steps)
        | Some (Solver.Counterexample _), _
          when obligation.locals <> [] || obligation.decisions <> [] -> (
            (* Where a counterexample is, the values of the locals there too,
               asked for only now, so that a query that proves keeps its
               key. *)
            match ask Made ~with_locals:true with
            | Answered (Solver.Counterexample _ as answer) -> Solved answer
            | Unanswered -> Pending_answer
            | Answered _ | No_query -> (
                match asked Made Exact with Some answer -> Solved answer | None -> Pending_answer))
        | Some answer, _ -> Solved answer)
  in
  (* Where an obligation is not proven, whether seeing the bodies hidden
     here would prove it, which is all its note about them is for. *)
  let solve index (obligation : Translate.obligation) choice =
    match solve index obligation choice with
    | Solved ((Solver.Counterexample _ | Solver.Out_of_steps) as answer)
      when obligation.hidden <> [] -> (
        match oracles.solve ~index ~choice ~variant:Revealed ~with_locals:false with
        | Answered Solver.Proven -> Solved_hidden answer
        | Answered _ | No_query -> Solved answer
        | Unanswered -> Pending_answer)
    | answer -> answer
  in
  let indexed = List.mapi (fun index obligation -> (index, obligation)) obligations in
  let bounded =
    List.filter (fun (_, (obligation : Translate.obligation)) -> obligation.constants <> []) indexed
  in
  let all_choices = choices obligations in
  (* The first choice that proves every bound, tried in order: a choice
     with a pending answer stops the search there. *)
  let chosen =
    let rec first = function
      | [] -> List.hd all_choices
      | choice :: rest ->
          let answers =
            List.map (fun (index, obligation) -> solve index obligation choice) bounded
          in
          if List.for_all (fun answer -> proven answer) answers then choice
          else if List.mem Pending_answer answers then choice
          else first rest
    in
    first all_choices
  in
  List.map (fun (index, obligation) -> (obligation, solve index obligation chosen)) indexed

(* An obligation's state: where it is, what it asks, where it was not
   shown, the diagnostic that says why, and whether its proof trusts
   compiled code. *)
type state = {
  code : Diagnostic.Code.prover;
  span : Diagnostic.span;
  shows : string;
  failure : Diagnostic.t option;
  trusts_compiled_code : bool;
}

let definition_states oracles database (key : Names.key) =
  let source_span span = source_span (within database key span) in
  match Query.demand database proof key with
  | Not_proven_here -> []
  | Unsupported (span, what) ->
      let message =
        Printf.sprintf "The prover cannot read %s yet, so nothing in this definition is proven."
          what
      in
      [
        ( {
            code = Unsupported;
            span = source_span span;
            shows = message;
            failure = Some (diagnostic Unsupported (source_span span) message);
            trusts_compiled_code = false;
          },
          None );
      ]
  | Obligations outcome ->
      List.map
        (fun ((obligation : Translate.obligation), (answer : answer)) ->
          let span = source_span obligation.span in
          (* These fixes change what the code means, so they are named, not
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
          (* A body that would have defined a callee is hidden from another
             package's proofs unless the callee is [transparent]: named where
             seeing it would prove the obligation. *)
          let answer, hidden_helps =
            match answer with
            | Solved_hidden answer -> (Solved answer, true)
            | answer -> (answer, false)
          in
          let hidden =
            if not hidden_helps then ""
            else
              let sentence markable =
                match List.filter (fun (_, can) -> can = markable) obligation.hidden with
                | [] -> ""
                | callees ->
                    Printf.sprintf
                      " The body of %s is not visible in this package, and with it this would be \
                       proven: give it %s."
                      (String.concat ", " (List.map (fun (name, _) -> "`" ^ name ^ "`") callees))
                      (if markable then
                         "an `ensures` that says what is needed, or make it a `public transparent \
                          fn`"
                       else "an `ensures` that says what is needed")
              in
              sentence true ^ sentence false
          in
          ( {
              code = obligation.code;
              span;
              shows = obligation.message;
              failure =
                (match answer with
                | Solved Proven | Solved_hidden _ | Ran_true | Pending_answer -> None
                | Ran_false -> failed " Running it on this template's text gives `false`."
                | Run_timed_out ->
                    failed
                      " Running it on this template's text took longer than the time limit, so it \
                       is not known."
                | Solved (Counterexample values) ->
                    failed
                      (counterexample (Logic.members obligation.query) obligation values ^ hidden)
                | Solved Out_of_steps ->
                    failed
                      (" The solver ran out of steps, so it may hold but needs help: a `proof` \
                        block or a theorem."
                      ^ (if Logic.untriggered obligation.query then
                           " A quantified fact it may need has no term for the solver to use it \
                            by, so an `assert` that names the term it is needed for may be enough."
                         else "")
                      ^ hidden));
              trusts_compiled_code =
                (match answer with
                | Ran_true -> true
                | Solved Proven -> given ~call:oracles.call obligation <> []
                | _ -> false);
            },
            obligation.cited ))
        (answers oracles outcome.obligations)

(* A request to an oracle, and the oracle's response, kept by the
   request's key. A run's response holds the key of the code that ran, so
   the driver can tell when the code has changed since. *)
type oracle_request = Solve of Solver.request | Run of run

type oracle_response =
  | Solver_response of Solver.canonical
  | Run_response of { code_key : string option; result : run_result }

let request_key = function
  | Solve request -> "solve " ^ Solver.request_key request
  | Run (Template_check evaluation) ->
      "template " ^ Digest.to_hex (Digest.string (Marshal.to_string evaluation []))
  | Run (Call call) -> "call " ^ Digest.to_hex (Digest.string (Marshal.to_string call []))

let oracle_response : (string, oracle_response) Query.input =
  Query.input ~name:"oracle_response" ~show:Fun.id ()

(* A definition's outcome: its states, once every response they need is
   recorded, or the requests still pending. *)
type outcome =
  | Decided of (state * (Names.key * Syntax.span) option) list
  | Pending of oracle_request list

let run_result database run =
  match Query.find database oracle_response (request_key (Run run)) with
  | Some (Run_response response) -> Some response.result
  | Some (Solver_response _) | None -> None

let call_value database call =
  match run_result database (Call call) with Some (Returned value) -> Some value | _ -> None

(* The runs a definition's proof needs: a saved result, so that the driver
   finds them in a later process without translating the definition. *)
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

type question = {
  definition : Names.key;
  index : int;
  choice : (S.t * (Z.t * Z.t)) list;
  variant : variant;
  with_locals : bool;
}

let show_question question =
  Printf.sprintf "%s #%d" (Names.show_key question.definition) question.index

(* One query an obligation may ask, rendered for the solver: a result of
   its own, found current when only the solver's responses changed, so a
   definition's outcome is derived again without rendering anything. *)
let question_request =
  Query.query ~name:"question_request" ~phase:Phases.verdicts ~saved:true ~show:show_question
    (fun database question ->
      match Query.demand database proof question.definition with
      | Obligations outcome -> (
          (* The question of whether seeing the hidden bodies would prove
             it is asked of the same obligation as its revealed proof made
             it. *)
          let obligations =
            if question.variant = Revealed then
              match Query.demand database revealed_proof question.definition with
              | Obligations revealed -> revealed.obligations
              | Not_proven_here | Unsupported _ -> []
            else outcome.obligations
          in
          match List.nth_opt obligations question.index with
          | Some obligation ->
              let values =
                List.map fst obligation.values
                @ if question.with_locals then List.map fst obligation.locals else []
              in
              (* With the locals, each [if]'s reach and condition, for the path
                 a counterexample takes. *)
              let terms =
                if question.with_locals then
                  List.concat
                    (List.mapi
                       (fun index (_, _, reached, condition) ->
                         [ (S.Reached index, reached); (S.Condition index, condition) ])
                       obligation.decisions)
                else []
              in
              Option.map
                (fun query -> Solver.request ~values ~terms query)
                (variant_query ~call:(call_value database) obligation question.choice
                   question.variant)
          | None -> None)
      | Not_proven_here | Unsupported _ -> None)

(* Each definition's outcome, derived from its obligations and the oracles'
   responses: a saved result, so a definition whose reads have not changed
   is neither translated nor asked anything again. A request whose response
   is not recorded is pending, and the outcome waits for it. The values of
   runs go into the solver's queries, so while any run is pending, only
   runs are requested: a query asked without their values would be one no
   later round asks. *)
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
                (fun ~index ~choice ~variant ~with_locals ->
                  match
                    Query.demand database question_request
                      { definition = key; index; choice; variant; with_locals }
                  with
                  | None -> No_query
                  | Some request -> (
                      match Query.find database oracle_response (request_key (Solve request)) with
                      | Some (Solver_response canonical) -> Answered (Solver.read request canonical)
                      | Some (Run_response _) | None ->
                          if not (List.mem (Solve request) !pending) then
                            pending := Solve request :: !pending;
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
let responses (evaluator : evaluator) solver requests =
  let solver_requests =
    List.filter_map (function Solve request -> Some request | Run _ -> None) requests
  in
  let answers = List.combine solver_requests (Solver.ask_all solver solver_requests) in
  List.map
    (fun request ->
      ( request_key request,
        match request with
        | Solve solver_request -> Solver_response (List.assq solver_request answers)
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

(* Each definition of the modules decided: the runs whose code changed are
   run again, the definitions' outcomes are asked for together, their
   pending requests are sent to the oracles together, and so on until none
   is pending, which takes a round or two, since an obligation asks again
   only after an answer such as running out of steps. *)
let solve_ahead ?(evaluator = no_evaluator) ~record database solver modules =
  let keys =
    List.concat_map
      (fun module_ ->
        List.filter_map
          (fun declaration ->
            let key = Names.key_of declaration in
            match Query.demand database Names.base key with Some _ -> Some key | None -> None)
          (Query.demand database Names.declarations module_))
      modules
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
      record (responses evaluator solver (List.sort_uniq compare (List.concat_map snd pending)));
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
let moved_states ?evaluator ~record database solver module_ =
  solve_ahead ?evaluator ~record database solver [ module_ ];
  List.filter_map
    (fun declaration ->
      let key = Names.key_of declaration in
      let base_of key = Option.map snd (Query.demand database Names.base key) in
      match base_of key with
      | Some base ->
          let moved offset (span : Diagnostic.span) =
            Source.span (span.start + offset) (span.stop + offset)
          in
          Some
            (List.map
               (fun (state, cited) ->
                 let note =
                   match cited with
                   | Some ((cited : Names.key), span) when cited.module_ = module_ ->
                       Option.map
                         (fun offset ->
                           ( moved offset (source_span (within database cited span)),
                             "This is the clause that must hold." ))
                         (base_of cited)
                   | _ -> None
                 in
                 (* A clause in another file is named by where it is, since a
                    note is in the diagnostic's own file. *)
                 let elsewhere =
                   match cited with
                   | Some ((cited : Names.key), span) when cited.module_ <> module_ -> (
                       match
                         ( base_of cited,
                           try Some (Query.demand database Workspace.file cited.module_)
                           with Not_found -> None )
                       with
                       | Some offset, Some file ->
                           let start =
                             (moved offset (source_span (within database cited span))).start
                           in
                           let line, _ = Source.position file.source start in
                           Printf.sprintf " The clause that must hold is at `%s:%d`."
                             (Source.path file.source) line
                       | _ -> "")
                   | _ -> ""
                 in
                 {
                   state with
                   span = moved base state.span;
                   failure =
                     Option.map
                       (fun failure ->
                         let failure = Diagnostic.move base failure in
                         let failure = { failure with message = failure.message ^ elsewhere } in
                         match note with
                         | Some note -> { failure with notes = failure.notes @ [ note ] }
                         | None -> failure)
                       state.failure;
                 })
               (decided database key))
      | None -> None)
    (Query.demand database Names.declarations module_)

let in_order list =
  List.sort
    (fun (left : Diagnostic.t) (right : Diagnostic.t) ->
      compare (left.span, left.code) (right.span, right.code))
    list

let states ?evaluator ~record database solver module_ =
  List.concat (moved_states ?evaluator ~record database solver module_)
  |> List.sort (fun left right -> compare (left.span, left.code) (right.span, right.code))

(* The failures among the states. The same failure on another path of one
   definition, as a second index into the same list with the same index
   is, is reported once. *)
let diagnostics ?evaluator ~record database solver module_ =
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
    (moved_states ?evaluator ~record database solver module_)
  |> in_order
