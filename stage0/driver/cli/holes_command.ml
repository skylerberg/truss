module Names = Resolve.Names

type hole = {
  definition : Path.t;
  file : string;
  line : int;
  column : int;
  type_ : string option;
  in_scope : (string * string) list;
  blocks : string list;
}

let of_declaration pipeline (names : Names.lookups) source (declaration : Names.declaration) =
  let key = Names.key_of declaration in
  match (names.definition key, names.place key, Pipeline.resolved pipeline key) with
  | Some definition, Some { base; _ }, Some resolved ->
      List.map
        (fun (hole : Inspect.hole) ->
          let source = Lazy.force source in
          let line, column = Source.position source (base + hole.offset) in
          {
            definition = declaration.path;
            file = Source.path source;
            line;
            column;
            type_ = hole.expected;
            in_scope = hole.scope;
            blocks = [];
          })
        (Inspect.holes definition resolved (Pipeline.tables pipeline key))
  | _ -> []

let gather snapshot packages pipeline paths =
  let names = Pipeline.names pipeline packages in
  List.concat_map
    (fun file ->
      let source = lazy (Command_packages.source snapshot packages file) in
      List.concat_map
        (fun (declaration : Names.declaration) ->
          if declaration.ordinal = 0 then of_declaration pipeline names source declaration else [])
        (names.declarations_in file))
    (Command_packages.selected snapshot packages paths)

let with_blocks snapshot packages pipeline holes =
  let roots =
    (match Program_command.mains pipeline packages with [ main ] -> [ ("main", main) ] | _ -> [])
    @ List.map
        (fun (test : Test_command.test) -> ("test " ^ Test_command.label test, test.path))
        (Test_command.select snapshot pipeline packages ~paths:[] ~match_:None)
  in
  let called =
    List.sort_uniq Path.compare
      (List.filter_map
         (fun hole -> if Option.is_some hole.type_ then Some hole.definition else None)
         holes)
  in
  let callers =
    if called = [] then []
    else
      List.map
        (fun viewer -> (viewer, Pipeline.callers pipeline ~viewer called))
        (List.sort_uniq Path.compare_package (List.map (fun (_, root) -> Path.package root) roots))
  in
  let calls (root : Path.t) definition =
    List.exists (Path.equal root) (List.assoc definition (List.assoc (Path.package root) callers))
  in
  let todo_types =
    if List.exists (fun hole -> hole.type_ = None) holes then
      let compile = Compiler.lowering_only pipeline packages in
      List.map (fun (_, root) -> (root, Compile.reached_todo_types compile root)) roots
    else []
  in
  let reaches_type root definition =
    List.exists (Path.equal definition) (List.assoc root todo_types)
  in
  List.map
    (fun hole ->
      let reaches = if hole.type_ = None then reaches_type else calls in
      {
        hole with
        blocks =
          List.filter_map
            (fun (label, root) -> if reaches root hole.definition then Some label else None)
            roots;
      })
    holes

let to_json hole =
  Json.Object
    [
      ("definition", Json.String (Path.show hole.definition));
      ("file", Json.String hole.file);
      ("line", Json.Int hole.line);
      ("column", Json.Int hole.column);
      ("kind", Json.String (if hole.type_ = None then "type" else "value"));
      ("type", Json.option (fun type_text -> Json.String type_text) hole.type_);
      ( "in_scope",
        Json.List
          (List.map
             (fun (name, ty) ->
               Json.Object [ ("name", Json.String name); ("type", Json.String ty) ])
             hole.in_scope) );
      ("blocks", Json.List (List.map (fun blocked -> Json.String blocked) hole.blocks));
    ]

let print hole =
  (match hole.type_ with
  | Some ty -> Output.printf "%s:%d:%d: hole of type %s\n" hole.file hole.line hole.column ty
  | None ->
      Output.printf "%s:%d:%d: the type %s is defined as todo\n" hole.file hole.line hole.column
        (Path.show hole.definition));
  if hole.in_scope <> [] then
    Output.printf "    in scope: %s\n"
      (String.concat ", " (List.map (fun (name, ty) -> name ^ ": " ^ ty) hole.in_scope));
  if hole.blocks <> [] then Output.printf "    blocks: %s\n" (String.concat "; " hole.blocks)

let run ~paths =
  let snapshot, packages = Command_packages.current () in
  let pipeline = Database.pipeline snapshot in
  let report = Report.gather pipeline snapshot packages in
  let holes =
    match gather snapshot packages pipeline paths with
    | [] -> []
    | holes -> with_blocks snapshot packages pipeline holes
  in
  if Output.json () then
    Json.print (Report.document report [ ("holes", Json.List (List.map to_json holes)) ])
  else begin
    Report.print report;
    List.iter print holes;
    if holes = [] then Output.print_line "No holes."
  end;
  if Report.clean report then 0 else 1
