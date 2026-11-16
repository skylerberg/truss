open Syntax
module Lookups = Lookups

type context = {
  resolved : Resolve.resolved;
  tables : Infer.tables;
  spans : Source.Definition_span.t array;
  text : string Lazy.t;
  mutable diagnostics : Diagnostic.in_definition list;
}

let report context ?(fixes = []) code (span : Source.Definition_span.t) message =
  context.diagnostics <-
    Diagnostic.make ~fixes ~code:(Usage code) span message :: context.diagnostics

let find_used_bindings (resolved : Resolve.resolved) =
  let is_used = Array.make (Array.length resolved.names) false in
  Array.iter (function Some (Resolve.Local id) -> is_used.(id) <- true | _ -> ()) resolved.names;
  is_used

let parameter_names (definition : definition) =
  let names = ref [] in
  let add (parameters : parameter list) =
    List.iter
      (fun (parameter : parameter) ->
        match parameter.kind with
        | Named_parameter { name; _ } -> names := name.id :: !names
        | _ -> ())
      parameters
  in
  (match definition.kind with
  | Function { signature; _ } | Method_declaration signature -> add signature.parameters
  | Theorem { parameters; _ } -> add parameters
  | Trait { members; _ } ->
      List.iter
        (fun (line : trait_member node) ->
          match line.kind with Law law -> add law.parameters | _ -> ())
        members
  | _ -> ());
  !names

let pattern_bindings (definition : definition) =
  let bindings = ref [] in
  let rec pattern ~is_bare_field (written : pattern) =
    match written.kind with
    | Binding name -> bindings := (name, is_bare_field) :: !bindings
    | Variant { fields = Some fields; _ } | Record fields -> pattern_fields fields
    | Alternatives alternatives -> List.iter (pattern ~is_bare_field) alternatives
    | _ -> ()
  and pattern_fields (fields : pattern_field list) =
    let has_several_fields =
      List.length (List.filter (fun (field : pattern_field) -> field.kind <> Rest) fields) > 1
    in
    List.iter
      (fun (field : pattern_field) ->
        match field.kind with
        | Named_field (_, inner) -> pattern ~is_bare_field:false inner
        | Field inner -> pattern ~is_bare_field:has_several_fields inner
        | Rest -> ())
      fields
  in
  let rec expression (value : expression) =
    (match value.kind with
    | Is { pattern = written; _ } -> pattern ~is_bare_field:false written
    | Lambda { parameters; _ } -> List.iter (pattern ~is_bare_field:false) parameters
    | Match { arms; _ } ->
        List.iter (fun (arm : arm) -> List.iter (pattern ~is_bare_field:false) arm.patterns) arms
    | Quantified { binder = Binder_in (written, _); _ } -> pattern ~is_bare_field:false written
    | _ -> ());
    Syntax_walk.expression_parts ~expression ~statement value
  and statement (written : statement) =
    (match written.kind with
    | Let { pattern = written_pattern; _ } | For { pattern = written_pattern; _ } ->
        pattern ~is_bare_field:false written_pattern
    | _ -> ());
    Syntax_walk.statement_parts ~expression ~statement written
  in
  Syntax_walk.definition ~statement expression definition;
  List.rev !bindings

let check_unused context (definition : definition) =
  let is_used = find_used_bindings context.resolved in
  let parameters = parameter_names definition in
  List.iter
    (fun ((name : name), is_bare_field) ->
      if
        context.resolved.names.(name.id) = Some Binding
        && (not (List.mem name.id parameters))
        && not is_used.(name.id)
      then
        let replacement = if is_bare_field then name.text ^ ": _" else "_" in
        let span = context.spans.(name.id) in
        report context Unused_variable span
          ~fixes:
            [
              Diagnostic.fix
                (Printf.sprintf "Write `%s`." replacement)
                [ Diagnostic.replace span replacement ];
            ]
          (Printf.sprintf "`%s` is never used. Bind it to `_` instead." name.text))
    (pattern_bindings definition)

let check_block context (written : block) =
  let rec check_statements = function
    | first :: (next :: _ as rest) ->
        if Infer.statement_diverges context.tables first then begin
          let last = List.nth rest (List.length rest - 1) in
          let unreachable = context.spans.(next.id) in
          let line_start = Source.fragment_line_start (Lazy.force context.text) unreachable.start in
          let deletion_start = if line_start > 0 then line_start - 1 else line_start in
          report context Unreachable_code unreachable
            ~fixes:
              [
                Diagnostic.fix "Delete the unreachable code."
                  [
                    Diagnostic.delete
                      (Source.Definition_span.make deletion_start context.spans.(last.id).stop);
                  ];
              ]
            "This code is unreachable: the statement before it diverges."
        end
        else check_statements rest
    | _ -> ()
  in
  check_statements written.statements

let check_unreachable context (definition : definition) =
  let rec expression (value : expression) =
    (match value.kind with
    | Block block | Lambda { body = block; _ } | Provide { body = block; _ } ->
        check_block context block
    | If { then_; else_; _ } -> (
        check_block context then_;
        match else_ with Some (Else block) -> check_block context block | _ -> ())
    | _ -> ());
    Syntax_walk.expression_parts ~expression ~statement value
  and statement (written : statement) =
    (match written.kind with
    | For { body; _ } | While { body; _ } | Proof body -> check_block context body
    | Parallel _ | Concurrent _ -> ()
    | Let { else_ = Some block; _ } -> check_block context block
    | _ -> ());
    Syntax_walk.statement_parts ~expression ~statement written
  in
  let bodies =
    match definition.kind with
    | Function { body; _ } | Test { body; _ } | Theorem { body; _ } | Law_proof { body; _ } ->
        [ body ]
    | Trait { members; _ } ->
        List.filter_map
          (fun (line : trait_member node) ->
            match line.kind with Law law -> Some law.body | _ -> None)
          members
    | _ -> []
  in
  List.iter (check_block context) bodies;
  Syntax_walk.definition ~statement expression definition

let check (lookups : Lookups.t) key =
  let definition = lookups.definition key in
  let context =
    {
      resolved = lookups.resolved key;
      tables = lookups.tables key;
      spans = lookups.spans key;
      text = lazy (lookups.text key);
      diagnostics = [];
    }
  in
  check_unused context definition;
  check_unreachable context definition;
  List.sort
    (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare left.span right.span)
    context.diagnostics
