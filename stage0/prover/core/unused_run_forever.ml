let run_forever_name = Language.Builtin_capability.show Run_forever

let names_run_forever (use : Syntax.capability_use) =
  match use.capability.kind with
  | Capability_path { path = { modules = []; last }; arguments = []; _ } ->
      last.text = run_forever_name
  | Capability_path _ | Self_capabilities _ | Associated_capabilities _ | Generic_capability _ ->
      false

let declares_run_forever (uses : Types.capability_set) =
  List.exists
    (fun capability -> Types.find_base capability = Built_in Run_forever)
    (Types.list_capabilities uses)

let has_written_measure (loop : Mir.loop) =
  List.exists (function Mir.Decreases _ -> true | Invariant _ | Cost _ -> false) loop.clauses

let rec has_default_measure (block : Mir.block) =
  List.exists
    (fun (statement : Mir.statement) ->
      (match statement.kind with
        | While { compared = Some _; loop; _ } -> not (has_written_measure loop)
        | _ -> false)
      || List.exists has_default_measure (Mir.list_nested_blocks statement))
    block.statements

let is_space character = character = ' ' || character = '\n' || character = '\r' || character = '\t'

let rec skip_spaces_before text position =
  if position > 0 && is_space text.[position - 1] then skip_spaces_before text (position - 1)
  else position

let rec skip_spaces_after text position =
  if position < String.length text && is_space text.[position] then
    skip_spaces_after text (position + 1)
  else position

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
  let locate_entry position = locate_use spans (List.nth uses position) in
  if List.length uses = 1 then
    let clause_span = Source.Definition_span.locate spans clause.id in
    let start = skip_spaces_before text clause_span.start in
    let brace = skip_spaces_after text clause_span.stop in
    let is_brace_on_own_line =
      brace < String.length text
      && text.[brace] = '{'
      && String.contains (String.sub text clause_span.stop (brace - clause_span.stop)) '\n'
    in
    if signature.clauses = [ clause ] && is_brace_on_own_line then
      Diagnostic.replace (Source.Definition_span.make start brace) " "
    else Diagnostic.delete (Source.Definition_span.make start clause_span.stop)
  else if index = 0 then
    Diagnostic.delete (Source.Definition_span.make (locate_entry 0).start (locate_entry 1).start)
  else
    Diagnostic.delete
      (Source.Definition_span.make (locate_entry (index - 1)).stop (locate_entry index).stop)

let list_run_forever_entries (signature : Syntax.signature) =
  List.concat_map
    (fun (clause : Syntax.clause) ->
      match clause.kind with
      | Uses uses ->
          List.concat
            (List.mapi
               (fun index use -> if names_run_forever use then [ (clause, uses, index) ] else [])
               uses)
      | Requires _ | Ensures _ | Decreases _ | Cost _ | Clause_error -> [])
    signature.clauses

let find (lookups : Lookups.t) (key : Resolve.Names.key) =
  let names = lookups.interface.names in
  let declares_run_forever () =
    match Interface.Impls.read_signature lookups.interface key.path with
    | Some (signature : Types.signature) -> declares_run_forever signature.uses
    | None -> Facts.raise_bug "%s has a body and no signature" (Path.show key.path)
  in
  let uses_run_forever () =
    lookups.requires_run_forever key
    || lookups.list_recursion_group
         (Mir.Call_edges.resolve_node
            { interface = lookups.interface; mir = lookups.mir }
            key.path Types.no_substitution)
       <> []
    ||
    match Mir.find_code (lookups.mir.read_body_part key) with
    | Some code -> has_default_measure code.body.code
    | None -> true
  in
  match (names.read_declaration key).kind with
  | (Function | Method) when declares_run_forever () && not (uses_run_forever ()) -> (
      match names.read_definition key with
      | { kind = Function { signature; _ }; _ } -> (
          match list_run_forever_entries signature with
          | [ (clause, uses, index) ] ->
              let spans = names.read_spans key in
              Some
                (Diagnostic.make ~severity:Warning ~code:(Usage Unused_run_forever)
                   ~fixes:
                     [
                       Diagnostic.fix "Remove `RunForever`"
                         [
                           make_removal ~text:(names.read_text key) ~spans signature clause uses
                             index;
                         ];
                     ]
                   (locate_use spans (List.nth uses index))
                   (Printf.sprintf
                      "Nothing in `%s` may run forever, so its `RunForever` is unused. Remove it."
                      (Path.show key.path)))
          | [] | _ :: _ :: _ -> None)
      | _ -> None)
  | _ -> None
