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

(* A value from the solver's model, written as Truss writes it. *)
let truss_value text =
  let length = String.length text in
  if length > 4 && String.sub text 0 3 = "(- " && text.[length - 1] = ')' then
    "-" ^ String.sub text 3 (length - 4)
  else text

let counterexample (values : (string * string) list) answer_values =
  let shown =
    List.filter_map
      (fun (symbol, name) ->
        Option.map
          (fun value -> Printf.sprintf "`%s` is %s" name (truss_value value))
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
                   (obligation.message ^ counterexample obligation.values values))
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
