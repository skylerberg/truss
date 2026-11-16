module Names = Resolve.Names
module Part = Database.Part

type direction = Dependents | Dependencies

let ends_path name shown =
  shown = name
  ||
  let name_length = String.length name and shown_length = String.length shown in
  shown_length > name_length
  && String.sub shown (shown_length - name_length) name_length = name
  && (shown.[shown_length - name_length - 1] = ':' || shown.[shown_length - name_length - 1] = '.')

let matches name (path : Path.t) =
  ends_path name (Path.show path)
  ||
  match path with
  | Method method_ -> ends_path name (Path.show (Method { method_ with receiver = Read }))
  | _ -> false

let definitions snapshot database name =
  let packages = List.map snd (Workspace.packages snapshot) in
  let names = Database.names database packages in
  List.sort_uniq Path.compare
    (List.concat_map
       (fun package ->
         List.filter_map
           (fun (declaration : Names.declaration) ->
             if declaration.ordinal = 0 && matches name declaration.path then Some declaration.path
             else None)
           (names.package_declarations package))
       packages)

type line = { reader : Path.t; read_kinds : string list; read : Path.t; reader_kinds : string list }

let grouped key value items =
  let groups = Hashtbl.create 16 in
  List.iter
    (fun item ->
      let group = key item in
      Hashtbl.replace groups group
        (value item :: Option.value (Hashtbl.find_opt groups group) ~default:[]))
    items;
  Hashtbl.fold
    (fun group values groups -> (group, List.sort_uniq compare values) :: groups)
    groups []

let lines (reads : Database.read list) =
  let reader_kinds_by_read =
    grouped
      (fun (reader, read_kind, read, _) -> (reader, read_kind, read))
      (fun (_, _, _, reader_kind) -> reader_kind)
      (List.filter_map
         (fun ({ dependent; dependency } : Database.read) ->
           match (Part.definition dependent, Part.definition dependency) with
           | Some reader, Some read ->
               Some (reader, Part.kind_name dependency, read, Part.kind_name dependent)
           | Some _, None | None, _ -> None)
         reads)
  in
  List.sort compare
    (List.map
       (fun ((reader, read, reader_kinds), read_kinds) ->
         { reader; read_kinds; read; reader_kinds })
       (grouped
          (fun ((reader, _, read), reader_kinds) -> (reader, read, reader_kinds))
          (fun ((_, read_kind, _), _) -> read_kind)
          reader_kinds_by_read))

let sentence line =
  Printf.sprintf "%s reads the %s of %s, in its %s" (Path.show line.reader)
    (Output.listed line.read_kinds) (Path.show line.read) (Output.listed line.reader_kinds)

let to_json line =
  let strings items = Json.List (List.map (fun item -> Json.String item) items) in
  Json.Object
    [
      ("reader", Json.String (Path.show line.reader));
      ("parts", strings line.reader_kinds);
      ("reads", strings line.read_kinds);
      ("of", Json.String (Path.show line.read));
    ]

let run ~direction ~name =
  let snapshot, _ = Command_packages.current () in
  let database = Workspace.open_database snapshot in
  match definitions snapshot database name with
  | [] -> Outcome.cannot_run "No definition named %s in this worktree." name
  | targets ->
      let lines =
        lines
          (match direction with
          | Dependents -> Database.dependents database targets
          | Dependencies -> Database.dependencies database targets)
      in
      if Output.json () then
        Json.print (Json.document ~diagnostics:[] [ ("reads", Json.List (List.map to_json lines)) ])
      else if lines = [] then
        Output.print_line
          (match direction with
          | Dependents -> "Nothing reads it."
          | Dependencies -> "It reads nothing.")
      else List.iter (fun line -> Output.print_line (sentence line)) lines;
      0
