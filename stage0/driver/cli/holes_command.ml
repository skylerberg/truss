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

let of_declaration snapshot packages database (names : Names.lookups)
    (declaration : Names.declaration) =
  let key = Names.key_of declaration in
  match
    (names.definition key, names.spans key, names.place key, Database.read_resolved database key)
  with
  | Some definition, Some spans, Some { file; base }, Some resolved ->
      let source = Command_packages.source snapshot packages file in
      List.map
        (fun (hole : Inspect.hole) ->
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
        (Inspect.holes spans definition resolved (Database.read_tables database key))
  | _ -> []

let gather snapshot packages database paths =
  let names = Database.make_name_lookups database packages in
  List.concat_map
    (fun file ->
      List.concat_map
        (fun (declaration : Names.declaration) ->
          if declaration.ordinal = 0 then
            of_declaration snapshot packages database names declaration
          else [])
        (names.declarations_in file))
    (Command_packages.selected snapshot packages paths)

let with_blocks snapshot packages database holes =
  let roots =
    (match Program_command.mains snapshot packages with [ main ] -> [ ("main", main) ] | _ -> [])
    @ List.map
        (fun (test : Test_command.test) -> ("test " ^ Test_command.label test, test.path))
        (Test_command.select snapshot database packages ~paths:[] ~match_:None)
  in
  let callers = Hashtbl.create 16 in
  let calls (root : Path.t) definition =
    let viewer = Path.package root in
    let reached =
      match Hashtbl.find_opt callers (viewer, definition) with
      | Some reached -> reached
      | None ->
          let reached = Database.list_callers database ~viewer definition in
          Hashtbl.replace callers (viewer, definition) reached;
          reached
    in
    List.exists (Path.equal root) reached
  in
  let compile = lazy (Compiler.lowering_only database packages) in
  let todo_types = Hashtbl.create 16 in
  let reaches_type root definition =
    let reached =
      match Hashtbl.find_opt todo_types root with
      | Some reached -> reached
      | None ->
          let reached = Compile.reached_todo_types (Lazy.force compile) root in
          Hashtbl.replace todo_types root reached;
          reached
    in
    List.exists (Path.equal definition) reached
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
  let database = Workspace.open_database snapshot in
  let report = Report.gather database snapshot packages in
  let holes =
    match gather snapshot packages database paths with
    | [] -> []
    | holes -> with_blocks snapshot packages database holes
  in
  if Output.json () then
    Json.print (Report.document report [ ("holes", Json.List (List.map to_json holes)) ])
  else begin
    Report.print report;
    List.iter print holes;
    if holes = [] then Output.print_line "No holes."
  end;
  if Report.clean report then 0 else 1
