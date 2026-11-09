(* The prover's entry point. See PROVER.md, "What the prover does". *)

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
              :: pair trait_generics interface.implements.trait_arguments )
      | None -> None)
  | _ -> None

let prove database (key : Names.key) =
  match (Query.demand database Names.definition key, Translate.callee_source database key) with
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
            Obligations
              {
                obligations =
                  List.concat_map (fun (o : Translate.outcome) -> o.obligations) outcomes;
                unproven_clauses =
                  List.concat_map (fun (o : Translate.outcome) -> o.unproven_clauses) outcomes;
              }
        | _ -> Not_proven_here
      with Translate.Unsupported (span, message) -> Unsupported (span, message))
  | _ -> Not_proven_here

let proof = Query.query ~name:"proof" ~show:Names.show_key prove

(* Messages *)

(* A value from the solver's model, written as Truss writes it: a negative
   number with its sign, and a datatype's value as its variant or record,
   with its fields in parentheses. *)
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
  let rec one = function
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

let definition_diagnostics database solver (key : Names.key) =
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
        (fun (obligation : Translate.obligation) ->
          match Solver.solve solver ~values:(List.map fst obligation.values) obligation.query with
          | Proven -> None
          | Counterexample values ->
              Some
                (diagnostic obligation.code (source_span obligation.span)
                   (obligation.message
                   ^ counterexample (Logic.members obligation.query) obligation.values values))
          | Out_of_steps ->
              Some
                (diagnostic obligation.code (source_span obligation.span)
                   (obligation.message
                  ^ " The solver ran out of steps, so it may hold but needs help: a `proof` block \
                     or a theorem.")))
        outcome.obligations
      @ List.map
          (fun (span, what) ->
            diagnostic Unsupported (source_span span)
              (Printf.sprintf "The prover does not prove %s yet." what))
          outcome.unproven_clauses

let diagnostics database solver module_ =
  Names.per_definition database module_ (definition_diagnostics database solver)
