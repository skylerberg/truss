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

type removal = Wildcard | Field_wildcard | Field_deletion of Source.Definition_span.t
type binding = { name : Syntax.name; removal : removal }

let collect_bindings context (definition : Syntax.definition) =
  let bindings = ref [] in
  let bind (name : Syntax.name) removal = bindings := { name; removal } :: !bindings in
  let rec pattern (written : Syntax.pattern) =
    match written.kind with
    | Binding name -> bind name Wildcard
    | Variant { fields = Some fields; _ } | Record fields -> pattern_fields fields
    | Alternatives alternatives -> List.iter pattern alternatives
    | _ -> ()
  and pattern_fields (fields : Syntax.pattern_field list) =
    let has_rest = List.exists (fun (field : Syntax.pattern_field) -> field.kind = Rest) fields in
    let has_several_fields =
      List.length (List.filter (fun (field : Syntax.pattern_field) -> field.kind <> Rest) fields)
      > 1
    in
    let rec bind_fields = function
      | [] -> ()
      | (field : Syntax.pattern_field) :: following ->
          (match (field.kind, following) with
          | Field { kind = Binding name; _ }, next :: _ when has_rest ->
              bind name
                (Field_deletion
                   (Source.Definition_span.make context.spans.(field.id).start
                      context.spans.(next.id).start))
          | Field { kind = Binding name; _ }, _ when has_rest || has_several_fields ->
              bind name Field_wildcard
          | (Named_field (_, inner) | Field inner), _ -> pattern inner
          | Rest, _ -> ());
          bind_fields following
    in
    bind_fields fields
  in
  let rec expression (value : Syntax.expression) =
    (match value.kind with
    | Is { pattern = written; _ } -> pattern written
    | Lambda { parameters; _ } -> List.iter pattern parameters
    | Match { arms; _ } -> List.iter (fun (arm : Syntax.arm) -> List.iter pattern arm.patterns) arms
    | Quantified { binder = Binder_in (written, _); _ } -> pattern written
    | _ -> ());
    Syntax_walk.expression_parts ~expression ~statement value
  and statement (written : Syntax.statement) =
    (match written.kind with
    | Let { pattern = written_pattern; _ } | For { pattern = written_pattern; _ } ->
        pattern written_pattern
    | _ -> ());
    Syntax_walk.statement_parts ~expression ~statement written
  in
  Syntax_walk.definition ~statement expression definition;
  List.rev !bindings

let describe_removal (binding : binding) =
  match binding.removal with
  | Wildcard -> ("Replace it with `_`.", "Write `_`.")
  | Field_wildcard ->
      let written = binding.name.text ^ ": _" in
      (Printf.sprintf "Match its field with `%s`." written, Printf.sprintf "Write `%s`." written)
  | Field_deletion _ ->
      ("Delete it, since `..` matches its field.", Printf.sprintf "Delete `%s`." binding.name.text)

let make_edit context (binding : binding) =
  let span = context.spans.(binding.name.id) in
  match binding.removal with
  | Wildcard -> Diagnostic.replace span "_"
  | Field_wildcard -> Diagnostic.replace span (binding.name.text ^ ": _")
  | Field_deletion field -> Diagnostic.delete field

let check_unused context (definition : Syntax.definition) =
  let targets = context.resolved.names in
  let bindings = collect_bindings context definition in
  let is_binding = Array.make (Array.length targets) false in
  List.iter (fun (binding : binding) -> is_binding.(binding.name.id) <- true) bindings;
  let is_used = Array.make (Array.length targets) false in
  Array.iteri
    (fun index target ->
      match target with
      | Some (Resolve.Local id) when not is_binding.(index) -> is_used.(id) <- true
      | _ -> ())
    targets;
  let rec find_first_alternative id =
    match targets.(id) with
    | Some (Resolve.Local first) when is_binding.(id) -> find_first_alternative first
    | _ -> id
  in
  let later_alternatives = Hashtbl.create 8 in
  List.iter
    (fun (binding : binding) ->
      let first = find_first_alternative binding.name.id in
      if first <> binding.name.id then Hashtbl.add later_alternatives first binding)
    bindings;
  List.iter
    (fun (binding : binding) ->
      let name = binding.name in
      if targets.(name.id) = Some Binding && not is_used.(name.id) then
        let occurrences = binding :: List.rev (Hashtbl.find_all later_alternatives name.id) in
        let instruction, title =
          match occurrences with
          | [ only ] -> describe_removal only
          | _ ->
              ( "Remove it from every alternative of the pattern.",
                Printf.sprintf "Remove `%s` from every alternative." name.text )
        in
        report context Unused_variable context.spans.(name.id)
          ~fixes:[ Diagnostic.fix title (List.map (make_edit context) occurrences) ]
          (Printf.sprintf "`%s` is never used. %s" name.text instruction))
    bindings

let check_block context (written : Syntax.block) =
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

let check_unreachable context (definition : Syntax.definition) =
  let rec expression (value : Syntax.expression) =
    (match value.kind with
    | Block block | Lambda { body = block; _ } | Provide { body = block; _ } ->
        check_block context block
    | If { then_; else_; _ } -> (
        check_block context then_;
        match else_ with Some (Else block) -> check_block context block | _ -> ())
    | _ -> ());
    Syntax_walk.expression_parts ~expression ~statement value
  and statement (written : Syntax.statement) =
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
          (fun (line : Syntax.trait_member Syntax.node) ->
            match line.kind with Law law -> Some law.body | _ -> None)
          members
    | _ -> []
  in
  List.iter (check_block context) bodies;
  Syntax_walk.definition ~statement expression definition

let check (lookups : Lookups.t) key =
  let definition = lookups.names.definition key in
  let context =
    {
      resolved = lookups.resolved key;
      tables = lookups.tables key;
      spans = lookups.names.spans key;
      text = lazy (lookups.names.text key);
      diagnostics = [];
    }
  in
  check_unused context definition;
  check_unreachable context definition;
  List.sort
    (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare left.span right.span)
    context.diagnostics
