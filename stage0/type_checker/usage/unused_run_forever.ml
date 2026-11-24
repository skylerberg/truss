let run_forever_name = Language.Builtin_capability.show Run_forever

let names_run_forever (use : Syntax.capability_use) =
  match use.capability.kind with
  | Capability_path { path = { modules = []; last }; arguments = []; _ } ->
      last.text = run_forever_name
  | Capability_path _ | Self_capabilities _ | Associated_capabilities _ | Generic_capability _ ->
      false

let contains_run_forever (uses : Types.capability_set) =
  List.exists
    (fun capability -> Types.find_base capability = Built_in Run_forever)
    (Types.list_capabilities uses)

let is_space character = character = ' ' || character = '\n' || character = '\r' || character = '\t'

let rec skip_spaces_before text position =
  if position > 0 && is_space text.[position - 1] then skip_spaces_before text (position - 1)
  else position

let rec skip_spaces_after text position =
  if position < String.length text && is_space text.[position] then
    skip_spaces_after text (position + 1)
  else position

let delete_clause ~text ~is_only_clause (clause : Source.Definition_span.t) =
  let start = skip_spaces_before text clause.start in
  let brace = skip_spaces_after text clause.stop in
  let is_brace_on_own_line =
    brace < String.length text
    && text.[brace] = '{'
    && String.contains (String.sub text clause.stop (brace - clause.stop)) '\n'
  in
  if is_only_clause && is_brace_on_own_line then
    Diagnostic.replace (Source.Definition_span.make start brace) " "
  else Diagnostic.delete (Source.Definition_span.make start clause.stop)

let locate_use spans (use : Syntax.capability_use) =
  let locate id = Source.Definition_span.locate spans id in
  let capability = locate use.capability.id in
  let stops =
    List.map
      (fun (bound : Syntax.bound_condition) -> (locate bound.id).stop)
      (Option.value use.unless ~default:[])
    @ List.map (fun (value : Syntax.expression) -> (locate value.id).stop) use.unless_values
  in
  Source.Definition_span.make capability.start (List.fold_left max capability.stop stops)

let make_removal ~text ~spans (signature : Syntax.signature) (clause : Syntax.clause)
    (uses : Syntax.capability_use list) index =
  if List.length uses = 1 then
    delete_clause ~text ~is_only_clause:(signature.clauses = [ clause ])
      (Source.Definition_span.locate spans clause.id)
  else Diagnostic.delete_list_entry (List.map (locate_use spans) uses) index

let list_run_forever_entries (signature : Syntax.signature) =
  List.concat_map
    (fun (clause : Syntax.clause) ->
      match clause.kind with
      | Uses uses ->
          List.concat
            (List.mapi
               (fun index use -> if names_run_forever use then [ (clause, uses, index) ] else [])
               uses)
      | Requires _ | Ensures _ | Decreases _ | Modifies _ | Cost _ | Clause_error -> [])
    signature.clauses

let find (lookups : Lookups.t) (key : Resolve.Names.key) (definition : Syntax.definition) =
  let names = lookups.interface.names in
  let declares_run_forever () =
    match Interface.Impls.read_signature lookups.interface key.path with
    | Some (signature : Types.signature) -> contains_run_forever signature.uses
    | None ->
        Compiler_bug.raise_bug ~stage:"Usage" "%s has a body and no signature" (Path.show key.path)
  in
  match ((names.read_declaration key).kind, definition.kind) with
  | (Function | Method), Function { signature; _ }
    when declares_run_forever ()
         && not (lookups.uses_run_forever key || lookups.is_recursive key.path) -> (
      match list_run_forever_entries signature with
      | [ (clause, uses, index) ] ->
          let spans = names.read_spans key in
          Some
            (Diagnostic.make ~severity:Warning ~code:(Usage Unused_run_forever)
               ~fixes:
                 [
                   Diagnostic.fix "Remove `RunForever`"
                     [ make_removal ~text:(names.read_text key) ~spans signature clause uses index ];
                 ]
               (locate_use spans (List.nth uses index))
               (Printf.sprintf
                  "Nothing in `%s` may run forever, so its `RunForever` is unused. Remove it."
                  (Path.show key.path)))
      | [] | _ :: _ :: _ -> None)
  | _ -> None
