type direction = Dependents | Dependencies

let list_definitions snapshot database argument =
  let packages = List.map snd (Workspace.list_packages snapshot) in
  let names = Database.make_name_lookups database in
  List.filter_map
    (function
      | Path_argument.Definition path when Option.is_some (names.find_key path) -> Some path
      | Package _ | Module _ | Definition _ -> None)
    (Path_argument.resolve names packages argument)

type line = { reader : Path.t; read_kinds : string list; read : Path.t; reader_kinds : string list }

module Kind_groups = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.t * string * Path.t
end))

module Reader_groups = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.t * Path.t * string list
end))

let group (type group) (module Groups : Hashtbl.S with type key = group) key_of value_of items =
  let groups = Groups.create 16 in
  List.iter
    (fun item ->
      let group = key_of item in
      Groups.replace groups group
        (value_of item :: Option.value (Groups.find_opt groups group) ~default:[]))
    items;
  Groups.fold
    (fun group values groups -> (group, List.sort_uniq compare values) :: groups)
    groups []

let list_lines (reads : Database.read list) =
  let reader_kinds_by_read =
    group
      (module Kind_groups)
      (fun (reader, read_kind, read, _) -> (reader, read_kind, read))
      (fun (_, _, _, reader_kind) -> reader_kind)
      (List.filter_map
         (fun ({ dependent; dependency } : Database.read) ->
           match
             (Database.Part.find_definition dependent, Database.Part.find_definition dependency)
           with
           | Some reader, Some read ->
               Some
                 ( reader,
                   Database.Part.show_kind dependency,
                   read,
                   Database.Part.show_kind dependent )
           | Some _, None | None, _ -> None)
         reads)
  in
  List.sort compare
    (List.map
       (fun ((reader, read, reader_kinds), read_kinds) ->
         { reader; read_kinds; read; reader_kinds })
       (group
          (module Reader_groups)
          (fun ((reader, _, read), reader_kinds) -> (reader, read, reader_kinds))
          (fun ((_, read_kind, _), _) -> read_kind)
          reader_kinds_by_read))

let describe_line line =
  Printf.sprintf "%s reads the %s of %s, in its %s" (Path.show line.reader)
    (Output.show_list line.read_kinds)
    (Path.show line.read)
    (Output.show_list line.reader_kinds)

let to_json line =
  let encode_strings items = Json.List (List.map (fun item -> Json.String item) items) in
  Json.Object
    [
      ("reader", Json.String (Path.show line.reader));
      ("parts", encode_strings line.reader_kinds);
      ("reads", encode_strings line.read_kinds);
      ("of", Json.String (Path.show line.read));
    ]

let run ~direction ~name =
  let argument = Path_argument.parse name in
  let snapshot, _ = Command_packages.load_current () in
  let database = Workspace.open_database snapshot in
  match list_definitions snapshot database argument with
  | [] -> Outcome.raise_cannot_run "No definition named %s is visible here." name
  | targets ->
      ignore
        (Database.prove database
           (List.concat_map
              (Workspace.list_package_files snapshot)
              (List.map snd (Workspace.list_packages snapshot))));
      let lines =
        list_lines
          (match direction with
          | Dependents -> Database.list_dependents database targets
          | Dependencies -> Database.list_dependencies database targets)
      in
      if Output.json () then
        Json.print
          (Json.make_document ~diagnostics:[] [ ("reads", Json.List (List.map to_json lines)) ])
      else if lines = [] then
        Output.print_line
          (match direction with
          | Dependents -> "Nothing reads it."
          | Dependencies -> "It reads nothing.")
      else List.iter (fun line -> Output.print_line (describe_line line)) lines;
      0
