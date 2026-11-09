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

let prove database (key : Names.key) =
  match (Query.demand database Names.definition key, Translate.callee_source database key) with
  | Some definition, Some source -> (
      try
        match definition.kind with
        | Function { signature; body } ->
            Obligations (Translate.function_ database source ~path:key.path signature body)
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
                      Some
                        (Translate.function_ database source ~path:(method_path key signature name)
                           signature body)
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
  let display name =
    match List.assoc_opt name members with
    | Some internal -> (
        (* [constructor.TYPE.VARIANT], or [.record] for a record. *)
        match List.rev (String.split_on_char '.' internal) with
        | "record" :: _ ->
            (* The type's own name: after its module, before its arguments. *)
            let type_ = String.sub internal 12 (String.length internal - 12 - 7) in
            let unqualified =
              match
                List.rev (String.split_on_char ':' (List.hd (String.split_on_char '[' type_)))
              with
              | last :: _ -> last
              | [] -> type_
            in
            unqualified
        | variant :: _ -> variant
        | [] -> internal)
    | None -> name
  in
  let opaque atom =
    (* The solver's name for a value of a sort it knows nothing about. *)
    match String.index_opt atom '!' with
    | Some _ -> true
    | None -> false
  in
  let rec one = function
    | `Atom atom :: rest when opaque atom -> ("a value the prover knows nothing more about", rest)
    | `Atom atom :: rest -> (display atom, rest)
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
        (display head ^ "(" ^ String.concat ", " items ^ ")", rest)
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
