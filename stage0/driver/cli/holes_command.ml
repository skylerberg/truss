module Path_table = Hashtbl.Make (Path)

type hole = {
  definition : Path.t;
  file : string;
  line : int;
  column : int;
  type_ : string option;
  in_scope : (string * string) list;
  blocks : string list;
}

let of_declaration snapshot packages database (names : Resolve.Names.lookups)
    (declaration : Resolve.Names.declaration) =
  let key = Resolve.Names.key_of declaration in
  match Database.read_resolved database key with
  | Some resolved ->
      let ({ file; base } : Resolve.Names.place) = names.place key in
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
        (Inspect.holes (names.spans key) (names.definition key) resolved
           (Option.map
              (fun (checked : Infer.checked) -> checked.tables)
              (Database.read_checked_body database key)))
  | None -> []

let gather snapshot packages database paths =
  let names = Database.make_name_lookups database packages in
  List.concat_map
    (fun file ->
      List.concat_map
        (fun (declaration : Resolve.Names.declaration) ->
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
  let compile = lazy (Compiler.lowering_only database packages) in
  let read_memoized table list_reached root =
    match Path_table.find_opt table root with
    | Some reached -> reached
    | None ->
        let reached = list_reached (Lazy.force compile) root in
        Path_table.replace table root reached;
        reached
  in
  let reached_definitions = Path_table.create 16 and reached_todo_types = Path_table.create 16 in
  List.map
    (fun hole ->
      let list_reached =
        if hole.type_ = None then read_memoized reached_todo_types Compile.list_reached_todo_types
        else read_memoized reached_definitions Compile.list_reached_definitions
      in
      {
        hole with
        blocks =
          List.filter_map
            (fun (label, root) ->
              if List.exists (Path.equal hole.definition) (list_reached root) then Some label
              else None)
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
