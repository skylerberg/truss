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

let list_holes snapshot database (names : Resolve.Names.lookups)
    (declaration : Resolve.Names.declaration) =
  let key = declaration.key in
  match Database.read_resolved database key with
  | Some resolved ->
      let ({ file; base } : Resolve.Names.place) = names.read_place key in
      let source = Command_packages.read_source snapshot database file in
      List.map
        (fun (hole : Inspect.hole) ->
          let line, column = Source.compute_position source (base + hole.offset) in
          {
            definition = key.path;
            file = Source.path source;
            line;
            column;
            type_ = hole.expected;
            in_scope = hole.scope;
            blocks = [];
          })
        (Inspect.list_holes (names.read_spans key) (names.read_definition key) resolved
           (Option.map
              (fun (checked : Infer.checked) -> checked.tables)
              (Database.read_checked_body database key)))
  | None -> []

let gather snapshot packages database paths =
  let names = Database.make_name_lookups database in
  List.concat_map
    (fun file ->
      List.concat_map
        (fun (declaration : Resolve.Names.declaration) ->
          if declaration.key.ordinal = 0 then list_holes snapshot database names declaration else [])
        (names.list_declarations_in file))
    (Command_packages.select_files snapshot packages paths)

let attach_blocks snapshot packages database holes =
  let lookups = lazy (Workspace_backend.require_lowered_lookups database packages) in
  let list_holes_relied_on main =
    let proofs =
      Proofs.check database snapshot packages
        (Command_packages.list_files snapshot
           (Command_packages.list_program_packages snapshot packages))
    in
    List.map
      (fun (file, line, column, _) -> (file, line, column))
      (Proofs.list_holes snapshot proofs
         ~reached:(Backend.list_reached_definitions (Lazy.force lookups) main))
  in
  let roots =
    (match Program_command.list_mains snapshot packages with
      | [ main ] -> [ ("main", main, list_holes_relied_on main) ]
      | _ -> [])
    @ List.map
        (fun (test : Test_command.test) -> ("test " ^ Test_command.label_test test, test.path, []))
        (Test_command.select snapshot database packages ~paths:[] ~match_:None)
  in
  let read_memoized table list_reached root =
    match Path_table.find_opt table root with
    | Some reached -> reached
    | None ->
        let reached = list_reached (Lazy.force lookups) root in
        Path_table.replace table root reached;
        reached
  in
  let reached_definitions = Path_table.create 16 and reached_todo_types = Path_table.create 16 in
  List.map
    (fun hole ->
      let list_reached =
        if hole.type_ = None then read_memoized reached_todo_types Backend.list_reached_todo_types
        else read_memoized reached_definitions Backend.list_reached_definitions
      in
      {
        hole with
        blocks =
          List.filter_map
            (fun (label, root, holes_relied_on) ->
              if
                List.exists (Path.equal hole.definition) (list_reached root)
                || List.mem (hole.file, hole.line, hole.column) holes_relied_on
              then Some label
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
      ("type", Json.encode_option (fun type_text -> Json.String type_text) hole.type_);
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
  let snapshot, packages = Command_packages.load_current () in
  let database = Workspace.open_database snapshot in
  let report = Report.gather database snapshot packages in
  let holes =
    match gather snapshot packages database paths with
    | [] -> []
    | holes -> attach_blocks snapshot packages database holes
  in
  if Output.json () then
    Json.print (Report.make_document report [ ("holes", Json.List (List.map to_json holes)) ])
  else begin
    Report.print report;
    List.iter print holes;
    if holes = [] then Output.print_line "No holes."
  end;
  if Report.has_errors report then 1 else 0
