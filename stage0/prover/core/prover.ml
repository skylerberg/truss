(* The prover's entry point. *)

open Syntax
module Translate = Translate
module Names = Resolve.Names
module L = Logic

type proof = Obligations of Translate.outcome | Unsupported of span * string | Not_proven_here

let method_path (key : Names.key) (signature : signature) name =
  let receiver : Path.receiver =
    match signature.parameters with
    | { kind = Self_parameter None; _ } :: _ -> Read
    | { kind = Self_parameter (Some Mut); _ } :: _ -> Mut
    | { kind = Self_parameter (Some Own); _ } :: _ -> Own
    | _ -> Static
  in
  Path.Method { owner = key.path; name; receiver }

(* The trait's clauses an [impl]'s method keeps, with the [impl]'s type as
   [Self] and its arguments for the trait's parameters. *)
let inherited database impl (signature : signature) name =
  match Query.demand database Interface.Environment.interface impl with
  | Some (Interface.Environment.Impl_interface interface) -> (
      match
        Translate.trait_part database interface.implements.trait name
          (Translate.receiver_of signature.parameters)
      with
      | Some (part, _) ->
          let trait_generics =
            match
              Query.demand database Interface.Environment.interface interface.implements.trait
            with
            | Some (Interface.Environment.Trait_interface trait) ->
                List.map (fun (generic : Types.generic) -> generic.generic) trait.trait_generics
            | _ -> []
          in
          let rec pair parameters arguments =
            match (parameters, arguments) with
            | parameter :: parameters, argument :: arguments ->
                (parameter, argument) :: pair parameters arguments
            | _ -> []
          in
          Some
            ( part,
              ( { Types.owner = interface.implements.trait; name = "Self" },
                Types.Type interface.for_type )
              :: pair trait_generics interface.implements.trait_arguments,
              Translate.provided_body database interface.implements.trait name
                (Translate.receiver_of signature.parameters) )
      | None -> None)
  | _ -> None

(* The [proof]s written for a trait's laws on a type, in the package: each
   law's name, with the proof's source and body. *)
let law_proofs database package trait (for_type : Types.ty) =
  let head = match for_type with Named { path; _ } -> Some path | _ -> None in
  match Workspace.package database package with
  | None -> []
  | Some { modules; _ } ->
      List.concat_map
        (fun module_ ->
          List.filter_map
            (fun (declaration : Names.declaration) ->
              let key = Names.key_of declaration in
              match
                ( Query.demand database Names.definition key,
                  Query.demand database Resolve.resolved key,
                  Translate.callee_source database key )
              with
              | ( Some { kind = Law_proof { trait_; law; type_; body }; _ },
                  Some resolved,
                  Some proof_source ) -> (
                  let named_trait =
                    match resolved.names.(trait_.path.last.id) with
                    | Some (Definition (_, path)) -> Path.equal path trait
                    | _ -> false
                  in
                  let named_type =
                    match (type_.kind, head) with
                    | Path_type written, Some head -> (
                        match resolved.names.(written.path.last.id) with
                        | Some (Definition (_, path)) -> Path.equal path head
                        | _ -> false)
                    | _ -> false
                  in
                  match (named_trait, named_type) with
                  | true, true -> Some (law.text, (proof_source, body))
                  | _ -> None)
              | _ -> None)
            (Query.demand database Names.declarations module_))
        modules

(* An [impl]'s obligation to keep each law of its trait. *)
let impl_laws database (key : Names.key) source (definition : definition) =
  match (Query.demand database Interface.Environment.interface key.path, definition.kind) with
  | Some (Interface.Environment.Impl_interface interface), Impl { trait_; _ } ->
      [
        Translate.laws database source ~impl:key.path ~trait:interface.implements.trait
          ~for_type:interface.for_type
          ~proofs:
            (law_proofs database (Path.package key.path) interface.implements.trait
               interface.for_type)
          ~at:trait_.span;
      ]
  | _ -> []

(* [standard::specification]'s contracts say what the mathematical
   collections are, so they are the trusted base, not obligations. *)
let specification (key : Names.key) =
  key.module_ = { package = "standard"; modules = [ "specification" ] }

let prove database (key : Names.key) =
  match (Query.demand database Names.definition key, Translate.callee_source database key) with
  | _ when specification key -> Not_proven_here
  | Some definition, Some source -> (
      try
        match definition.kind with
        | Function { signature; body } ->
            let updating_helper =
              definition.visibility = Private
              && (match signature.name with Member_name _ -> true | Plain_name _ -> false)
              && Translate.receiver_of signature.parameters = Mut
            in
            Obligations
              (Translate.function_ ~updating_helper database source ~path:key.path signature body)
        | Test { body; _ } -> Obligations (Translate.test database source ~path:key.path body)
        | Theorem { parameters; clauses; body; _ } ->
            Obligations (Translate.theorem database source ~path:key.path ~parameters ~clauses body)
        | Impl { members; _ } ->
            let outcomes =
              List.filter_map
                (fun (member : impl_member line) ->
                  match member.kind with
                  | Impl_method { signature; body } ->
                      let name =
                        match signature.name with
                        | Plain_name name | Member_name (_, name) -> name.text
                      in
                      let inherited = inherited database key.path signature name in
                      Some
                        (Translate.function_ ?inherited database source
                           ~path:(method_path key signature name) signature body)
                  | _ -> None)
                members
            in
            let outcomes = outcomes @ impl_laws database key source definition in
            Obligations
              {
                obligations =
                  List.concat_map (fun (o : Translate.outcome) -> o.obligations) outcomes;
                holes = List.concat_map (fun (o : Translate.outcome) -> o.holes) outcomes;
              }
        | Type_definition { clauses; _ } -> (
            match
              List.find_map
                (fun (clause : type_clause) ->
                  match clause.kind with Potential written -> Some written | _ -> None)
                clauses
            with
            | Some written ->
                Obligations (Translate.type_potential database source ~path:key.path ~written)
            | None -> Not_proven_here)
        | _ -> Not_proven_here
      with
      | Translate.Unsupported (span, message) -> Unsupported (span, message)
      | Translate.Foreign_unsupported message -> Unsupported (Syntax.Span.make 0 0, message))
  | _ -> Not_proven_here

let proof = Query.query ~phase:Proofs ~name:"proof" ~show:Names.show_key prove

(* Messages *)

(* A value from the solver's model, written as Truss writes it: a negative
   number with its sign, and a datatype's value as its variant or record,
   with its fields in parentheses. *)
(* A float from the solver's model, as Truss writes it: the shortest
   decimal that reads back as the same bits, with a point. *)
let float_text bits =
  let shortest digits_for read =
    let rec go digits =
      let text = Printf.sprintf "%.*g" digits read in
      if digits >= 17 || float_of_string text = read then text else go (digits + 1)
    in
    go digits_for
  in
  let text =
    match String.length bits with
    | 64 -> shortest 1 (Int64.float_of_bits (Int64.of_string ("0b" ^ bits)))
    | 32 ->
        let value = Int32.float_of_bits (Int32.of_string ("0b" ^ bits)) in
        let rec go digits =
          let text = Printf.sprintf "%.*g" digits value in
          if digits >= 9 || Int32.bits_of_float (float_of_string text) = Int32.bits_of_float value
          then text
          else go (digits + 1)
        in
        go 1
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
  (* The last part of a prover name: a variant's name, or a field's. *)
  let last internal =
    match List.rev (String.split_on_char '.' internal) with last :: _ -> last | [] -> internal
  in
  (* A constructor's name as Truss writes it: its variant, or for a record
     its type's own name, after its module and before its arguments. *)
  let constructor internal =
    if last internal = "record" then
      let type_ = String.sub internal 12 (String.length internal - 12 - 7) in
      match List.rev (String.split_on_char ':' (List.hd (String.split_on_char '[' type_))) with
      | last :: _ -> last
      | [] -> type_
    else last internal
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
                  (List.map2 (fun field item -> last field ^ ": " ^ item) fields items)
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

let counterexample members (values : (string * string) list) answer_values =
  let shown =
    List.filter_map
      (fun (symbol, name) ->
        Option.map
          (fun value -> Printf.sprintf "`%s` is %s" name (truss_value members value))
          (List.assoc_opt symbol answer_values))
      (List.rev values)
  in
  match shown with [] -> "" | shown -> " For example, when " ^ String.concat ", " shown ^ "."

let diagnostic code span message = Diagnostic.make ~code:(Diagnostic.Code.Prover code) span message
let source_span (span : span) : Diagnostic.span = Source.span span.start span.stop

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
   decides it gave, or that it ran past its time limit. *)
type answer = Solved of Solver.answer | Ran_false | Ran_too_long
type evaluated = Holds | Fails | Too_long

let bitwise_operations = [ "and"; "or"; "xor"; "complement"; "shift_left"; "shift_right" ]

let integer_width = function
  | "Int8" -> Some (8, true)
  | "Int16" -> Some (16, true)
  | "Int32" -> Some (32, true)
  | "Int64" | "ISize" -> Some (64, true)
  | "UInt8" -> Some (8, false)
  | "UInt16" -> Some (16, false)
  | "UInt32" -> Some (32, false)
  | "UInt64" | "USize" -> Some (64, false)
  | _ -> None

let bitwise_of name =
  match String.split_on_char '.' name with
  | [ "operation"; operation; type_ ] when List.mem operation bitwise_operations ->
      Option.map (fun (bits, signed) -> (operation, bits, signed)) (integer_width type_)
  | _ -> None

let exactly (query : L.query) =
  let found = ref [] in
  let rec walk = function
    | L.Apply (name, arguments) as term ->
        if bitwise_of name <> None && not (List.mem term !found) then found := term :: !found;
        List.iter walk arguments
    | L.Forall (_, body) | L.Exists (_, body) -> walk body
    | L.Symbol _ | L.Integer _ | L.Boolean _ | L.Bits _ -> ()
  in
  List.iter walk (query.goal :: query.facts);
  let defined term =
    match term with
    | L.Apply (name, arguments) -> (
        match (bitwise_of name, arguments) with
        | Some (operation, bits, signed), first :: rest ->
            let bits_of value = L.Apply (Printf.sprintf "(_ int2bv %d)" bits, [ value ]) in
            let a = bits_of first in
            let result =
              match (operation, rest) with
              | "complement", _ -> Some (L.Apply ("bvnot", [ a ]))
              | "and", [ b ] -> Some (L.Apply ("bvand", [ a; bits_of b ]))
              | "or", [ b ] -> Some (L.Apply ("bvor", [ a; bits_of b ]))
              | "xor", [ b ] -> Some (L.Apply ("bvxor", [ a; bits_of b ]))
              | "shift_left", [ b ] -> Some (L.Apply ("bvshl", [ a; bits_of b ]))
              | "shift_right", [ b ] ->
                  Some (L.Apply ((if signed then "bvashr" else "bvlshr"), [ a; bits_of b ]))
              | _ -> None
            in
            Option.map
              (fun result ->
                let unsigned = L.Apply ("bv2nat", [ result ]) in
                let value =
                  if signed then
                    let half = L.Integer (Z.shift_left Z.one (bits - 1)) in
                    L.ite
                      (L.Apply (">=", [ unsigned; half ]))
                      (L.Apply ("-", [ unsigned; L.Integer (Z.shift_left Z.one bits) ]))
                      unsigned
                  else unsigned
                in
                L.equal term value)
              result
        | _ -> None)
    | _ -> None
  in
  match List.filter_map defined (List.rev !found) with
  | [] -> None
  | definitions -> Some { query with facts = query.facts @ definitions }

(* Each obligation's answer. One that mentions the constants of [O(...)]
   bounds is asked with each choice of a pair for every bound in turn, the
   same choice for all of them, since a recursive call assumes the bound
   with the constants it is shown with; the first choice that proves them
   all is taken, and if none does, the answers are the first choice's. *)
(* Running compiled code, which the caller gives, since the prover does
   not depend on code generation: a template's check, and a call whose
   arguments are known, whose result is a [Bool] as 0 or 1. *)
type running = {
  template : Translate.evaluation -> evaluated option;
  call : Translate.known_call -> Z.t option;
}

let not_running = { template = (fun _ -> None); call = (fun _ -> None) }

let answers ?(running = not_running) solver (obligations : Translate.obligation list) =
  (* What running code gives of the calls a query mentions, as facts, which
     are only as true as the compiled code, which the prover trusts. *)
  let given (obligation : Translate.obligation) =
    List.filter_map
      (fun (known : Translate.known_call) ->
        Option.map
          (fun value ->
            L.equal known.term
              (if known.result_is_bool then L.Boolean (not (Z.equal value Z.zero))
               else L.Integer value))
          (running.call known))
      obligation.known_calls
  in
  let solve (obligation : Translate.obligation) choice =
    let pins =
      List.map
        (fun (constants : Costs.constants) ->
          Costs.pin constants (List.assoc constants.factor choice))
        obligation.constants
    in
    let query =
      { obligation.query with facts = obligation.query.facts @ pins @ given obligation }
    in
    let values = List.map fst obligation.values in
    (* A clause running code decides is decided so, and the solver never
       asked. *)
    match Option.bind obligation.evaluation running.template with
    | Some Holds -> Solved Proven
    | Some Fails -> Ran_false
    | Some Too_long -> Ran_too_long
    | None -> (
        match Solver.solve solver ~values query with
        | Proven -> Solved Proven
        | first -> (
            match exactly query with
            | Some exact -> Solved (Solver.solve solver ~values exact)
            | None -> Solved first))
  in
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
  let rec choices = function
    | [] -> [ [] ]
    | (constants : Costs.constants) :: rest ->
        List.concat_map
          (fun pair -> List.map (fun choice -> (constants.factor, pair) :: choice) (choices rest))
          constants.pairs
  in
  let bounded =
    List.filter (fun (obligation : Translate.obligation) -> obligation.constants <> []) obligations
  in
  let all_choices = choices groups in
  let chosen =
    match
      List.find_opt
        (fun choice ->
          List.for_all (fun obligation -> solve obligation choice = Solved Proven) bounded)
        all_choices
    with
    | Some choice -> choice
    | None -> List.hd all_choices
  in
  List.map (fun obligation -> (obligation, solve obligation chosen)) obligations

let definition_diagnostics ?running database solver (key : Names.key) =
  let source_span span = source_span (within database key span) in
  match Query.demand database proof key with
  | Not_proven_here -> []
  | Unsupported (span, what) ->
      [
        diagnostic Unsupported (source_span span)
          (Printf.sprintf "The prover cannot read %s yet, so nothing in this definition is proven."
             what);
      ]
  | Obligations outcome ->
      List.filter_map
        (fun ((obligation : Translate.obligation), (answer : answer)) ->
          match answer with
          | Solved Proven -> None
          | Ran_false ->
              Some
                (diagnostic obligation.code (source_span obligation.span)
                   (obligation.message ^ " Running it on this template's text gives `false`."))
          | Ran_too_long ->
              Some
                (diagnostic obligation.code (source_span obligation.span)
                   (obligation.message
                  ^ " Running it on this template's text took longer than the time limit, so it is \
                     not known."))
          | Solved (Counterexample values) ->
              Some
                (diagnostic obligation.code (source_span obligation.span)
                   (obligation.message
                   ^ counterexample (Logic.members obligation.query) obligation.values values))
          | Solved Out_of_steps ->
              Some
                (diagnostic obligation.code (source_span obligation.span)
                   (obligation.message
                  ^ " The solver ran out of steps, so it may hold but needs help: a `proof` block \
                     or a theorem.")))
        (answers ?running solver outcome.obligations)

let diagnostics ?running database solver module_ =
  Names.per_definition database module_ (definition_diagnostics ?running database solver)
