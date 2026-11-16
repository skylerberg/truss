type direction = Dependents | Dependencies

let has_suffix names ~suffix =
  let skipped = List.length names - List.length suffix in
  skipped >= 0 && List.filteri (fun index _ -> index >= skipped) names = suffix

let matches (argument : Path_argument.t) (path : Path.t) =
  let suffix = argument.prefix @ [ argument.last ] in
  let is_named (module_ : Path.module_) name =
    has_suffix (Path.list_module_parts module_ @ [ name ]) ~suffix
  in
  match (path, argument.member) with
  | Top { module_; name }, None -> is_named module_ name
  | (Method { owner; name; _ } | Member_constant { owner; name }), Some member -> (
      name = member
      &&
      match owner with
      | Top { module_; name } | Impl { for_type = Top { module_; name }; _ } ->
          is_named module_ name
      | _ -> false)
  | (Method { name; _ } | Member_constant { name; _ }), None ->
      argument.prefix = [] && name = argument.last
  | _ -> false

let find_definitions snapshot database argument =
  let packages = List.map snd (Workspace.list_packages snapshot) in
  let names = Database.make_name_lookups database packages in
  List.sort_uniq Path.compare
    (List.concat_map
       (fun package ->
         List.filter_map
           (fun (declaration : Resolve.Names.declaration) ->
             if declaration.ordinal = 0 && matches argument declaration.path then
               Some declaration.path
             else None)
           (names.list_package_declarations package))
       packages)

type line = { reader : Path.t; read_kinds : string list; read : Path.t; reader_kinds : string list }

module Kind_groups = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.t * string * Path.t
end))

module Reader_groups = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.t * Path.t * string list
end))

let group (type group) (module Groups : Hashtbl.S with type key = group) key value items =
  let groups = Groups.create 16 in
  List.iter
    (fun item ->
      let group = key item in
      Groups.replace groups group
        (value item :: Option.value (Groups.find_opt groups group) ~default:[]))
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
  let strings items = Json.List (List.map (fun item -> Json.String item) items) in
  Json.Object
    [
      ("reader", Json.String (Path.show line.reader));
      ("parts", strings line.reader_kinds);
      ("reads", strings line.read_kinds);
      ("of", Json.String (Path.show line.read));
    ]

let run ~direction ~name =
  let argument = Path_argument.parse name in
  let snapshot, _ = Command_packages.load_current () in
  let database = Workspace.open_database snapshot in
  match find_definitions snapshot database argument with
  | [] -> Outcome.raise_cannot_run "No definition named %s in this worktree." name
  | targets ->
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
