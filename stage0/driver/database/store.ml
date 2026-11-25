type schema = Main | Attached of string

type t = {
  sql : Sql.t;
  mutable attached : (string * string) list;
  mutable routes : (Path.package * string) list;
  mutable project : Path.package list;
  mutable attachment_count : int;
}

type cell = Sql.argument = Blob of string | Text of string | Integer of int | Null

let name_schema = function Main -> "main" | Attached name -> name
let identify key = Int64.to_int (String.get_int64_le (Digest.BLAKE128.string key) 0)
let wrap sql = { sql; attached = []; routes = []; project = []; attachment_count = 0 }

let empty_database =
  lazy
    (let sql = Sql.open_memory () in
     Sql.run_script sql (Schema.make_script ~schema:"main");
     sql)

let create_memory () =
  let store = wrap (Sql.open_memory ()) in
  Sql.copy_into ~source:(Lazy.force empty_database) ~schema:"main" store.sql;
  Sql.begin_transaction store.sql;
  store

let open_file path =
  let store = wrap (Sql.open_file path) in
  if not (Sql.has_row store.sql "SELECT 1 FROM main.sqlite_master WHERE name = 'definition'" [])
  then Sql.run_script store.sql (Schema.make_script ~schema:"main");
  Sql.begin_transaction store.sql;
  store

let attach store path =
  match List.assoc_opt path store.attached with
  | Some name -> Attached name
  | None ->
      let name = Printf.sprintf "loaded_%d" store.attachment_count in
      store.attachment_count <- store.attachment_count + 1;
      Sql.attach_immutable_file store.sql ~schema:name path;
      store.attached <- store.attached @ [ (path, name) ];
      Attached name

let detach store path =
  match List.assoc_opt path store.attached with
  | Some name ->
      Sql.detach store.sql ~schema:name;
      store.attached <- List.remove_assoc path store.attached;
      store.routes <- List.filter (fun (_, routed) -> routed <> name) store.routes
  | None -> ()

let list_attached store = List.map fst store.attached

let locate_attached store path =
  Option.map (fun name -> Attached name) (List.assoc_opt path store.attached)

let replace_routes store routes =
  store.routes <-
    List.filter_map
      (fun (package, schema) ->
        match schema with Attached name -> Some (package, name) | Main -> None)
      routes

let list_project store = store.project
let replace_project store project = store.project <- project

let locate_schema store package =
  if List.mem package store.project then Main
  else match List.assoc_opt package store.routes with Some name -> Attached name | None -> Main

let copy store =
  let copied = wrap (Sql.open_memory ()) in
  Sql.copy_into ~source:store.sql ~schema:"main" copied.sql;
  Sql.begin_transaction copied.sql;
  copied.routes <-
    List.concat_map
      (fun (path, name) ->
        let schema = attach copied path in
        List.filter_map
          (fun (package, routed) ->
            if routed = name then Some (package, name_schema schema) else None)
          store.routes)
      store.attached;
  copied.project <- store.project;
  copied

let copy_file path =
  let source = Sql.open_immutable_file path in
  let copied = wrap (Sql.open_memory ()) in
  Fun.protect
    ~finally:(fun () -> Sql.close source)
    (fun () -> Sql.copy_into ~source ~schema:"main" copied.sql);
  Sql.begin_transaction copied.sql;
  copied

let commit store =
  Sql.commit_transaction store.sql;
  Sql.checkpoint store.sql;
  Sql.begin_transaction store.sql

let close store =
  Sql.commit_transaction store.sql;
  Sql.checkpoint store.sql;
  Sql.close store.sql

let close_uncommitted store =
  Sql.roll_back_transaction store.sql;
  Sql.close store.sql

let save store ~into =
  let temporary = Printf.sprintf "%s.%d.tmp" into (Unix.getpid ()) in
  (try Sys.remove temporary with Sys_error _ -> ());
  Sql.run_outside_transaction store.sql (fun () ->
      Sql.run store.sql "VACUUM main INTO ?1" [ Text temporary ]);
  Unix.rename temporary into

let read_cells count row = Array.init count (Sql.read_cell row)

let make_condition key =
  String.concat " AND "
    (List.mapi (fun index (column, _) -> Printf.sprintf "\"%s\" = ?%d" column (index + 1)) key)

let find_row store schema ~table ~key ~columns =
  Sql.find_row store.sql
    (Printf.sprintf "SELECT %s FROM %s.\"%s\" WHERE %s"
       (String.concat ", " (List.map (Printf.sprintf "\"%s\"") columns))
       (name_schema schema) table (make_condition key))
    (List.map snd key)
    (read_cells (List.length columns))

let replace_row store ~table cells =
  Sql.run store.sql
    (Printf.sprintf "INSERT OR REPLACE INTO main.\"%s\" (%s) VALUES (%s)" table
       (String.concat ", " (List.map (fun (column, _) -> Printf.sprintf "\"%s\"" column) cells))
       (String.concat ", " (List.mapi (fun index _ -> Printf.sprintf "?%d" (index + 1)) cells)))
    (List.map snd cells)

let find_meta store name =
  Option.map
    (fun cells -> match cells.(0) with Blob value -> value | _ -> "")
    (find_row store Main ~table:"meta" ~key:[ ("name", Text name) ] ~columns:[ "value" ])

let write_meta store name value =
  replace_row store ~table:"meta" [ ("name", Text name); ("value", Blob value) ]

type fact = {
  table : string;
  columns : string list;
  fixed : cell list;
  condition : string;
  find_stored_text : string;
  replace_text : string;
  remove_text : string;
  guard : (string * string) option;
  mutable find_texts : (string * string) list;
}

let quote_columns columns = String.concat ", " (List.map (Printf.sprintf "\"%s\"") columns)

let make_fact ~table ~id_column ~fixed ~columns =
  let key_columns = id_column :: List.map fst fixed in
  let condition =
    String.concat " AND "
      (List.mapi (fun index column -> Printf.sprintf "\"%s\" = ?%d" column (index + 1)) key_columns)
  in
  let written = key_columns @ columns in
  {
    table;
    columns;
    fixed = List.map snd fixed;
    condition;
    find_stored_text =
      Printf.sprintf "SELECT %s FROM main.\"%s\" WHERE %s" (quote_columns columns) table condition;
    replace_text =
      Printf.sprintf "INSERT INTO main.\"%s\" (%s) VALUES (%s) ON CONFLICT (%s) DO UPDATE SET %s"
        table (quote_columns written)
        (String.concat ", " (List.mapi (fun index _ -> Printf.sprintf "?%d" (index + 1)) written))
        (quote_columns key_columns)
        (String.concat ", "
           (List.map
              (fun column -> Printf.sprintf "\"%s\" = excluded.\"%s\"" column column)
              columns));
    remove_text = Printf.sprintf "DELETE FROM main.\"%s\" WHERE %s" table condition;
    guard = None;
    find_texts = [];
  }

let guard_fact fact ~table ~id_column =
  { fact with guard = Some (table, id_column); find_texts = [] }

type 'row current = Current of 'row | Absent | Stale

let find_fact store schema fact ~id ~stages =
  let schema = name_schema schema in
  let text =
    match List.assoc_opt schema fact.find_texts with
    | Some text -> text
    | None ->
        let guards =
          List.map
            (fun (table, id_column) ->
              ( Printf.sprintf "(SELECT \"state\" FROM %s.\"%s\" WHERE \"%s\" = ?1)" schema table
                  id_column,
                "NULL" ))
            (Option.to_list fact.guard)
        in
        let nulls =
          String.concat ", " (List.map (fun _ -> "NULL") fact.columns @ List.map snd guards)
        in
        let text =
          String.concat " UNION ALL "
            (Printf.sprintf "SELECT 0, %s FROM %s.\"%s\" WHERE %s"
               (String.concat ", " (quote_columns fact.columns :: List.map fst guards))
               schema fact.table fact.condition
            :: List.mapi
                 (fun index _ ->
                   Printf.sprintf "SELECT 1, %s FROM main.stale WHERE stage = ?%d AND id = ?1" nulls
                     (List.length fact.fixed + 2 + index))
                 stages)
        in
        fact.find_texts <- (schema, text) :: fact.find_texts;
        text
  in
  let count = List.length fact.columns + List.length (Option.to_list fact.guard) in
  let rows =
    Sql.list_rows store.sql text
      ((Integer id :: fact.fixed) @ List.map (fun stage -> Integer stage) stages)
      (fun row ->
        (Sql.read_integer row 0 = 1, Array.init count (fun index -> Sql.read_cell row (index + 1))))
  in
  if List.exists fst rows then Stale
  else match rows with (_, cells) :: _ -> Current cells | [] -> Absent

let find_stored_fact store fact ~id =
  Sql.find_row store.sql fact.find_stored_text (Integer id :: fact.fixed)
    (read_cells (List.length fact.columns))

let replace_fact store fact ~id cells =
  Sql.run store.sql fact.replace_text ((Integer id :: fact.fixed) @ cells)

let remove_fact store fact ~id = Sql.run store.sql fact.remove_text (Integer id :: fact.fixed)

type diagnostic = {
  definition : int option;
  file : int option;
  is_error : bool;
  code : string;
  start : int;
  stop : int;
  message : string;
  detail : string;
}

let encode_optional = function Some value -> Integer value | None -> Null

let list_unit_diagnostics store schema ~stage ~unit =
  Sql.list_rows store.sql
    (Printf.sprintf
       "SELECT definition, detail FROM %s.diagnostic WHERE stage = ?1 AND unit = ?2 ORDER BY \
        position"
       (name_schema schema))
    [ Integer stage; Integer unit ]
    (fun row ->
      ((if Sql.is_null row 0 then None else Some (Sql.read_integer row 0)), Sql.read_blob row 1))

let has_diagnostic store ~stage ~unit =
  Sql.has_row store.sql "SELECT 1 FROM main.diagnostic WHERE stage = ?1 AND unit = ?2 LIMIT 1"
    [ Integer stage; Integer unit ]

let mark_reported_units_stale store ~stage =
  Sql.run store.sql
    "INSERT OR IGNORE INTO main.stale (stage, id) SELECT DISTINCT stage, unit FROM main.diagnostic \
     WHERE stage = ?1"
    [ Integer stage ]

let replace_diagnostics store ~stage ~unit ~package diagnostics =
  let is_changed =
    list_unit_diagnostics store Main ~stage ~unit
    <> List.map (fun diagnostic -> (diagnostic.definition, diagnostic.detail)) diagnostics
  in
  if is_changed then begin
    Sql.run store.sql "DELETE FROM main.diagnostic WHERE stage = ?1 AND unit = ?2"
      [ Integer stage; Integer unit ];
    List.iteri
      (fun position diagnostic ->
        Sql.run store.sql
          "INSERT INTO main.diagnostic (stage, unit, position, package, definition, file, \
           severity, code, start, stop, message, detail) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, \
           ?9, ?10, ?11, ?12)"
          [
            Integer stage;
            Integer unit;
            Integer position;
            Text package;
            encode_optional diagnostic.definition;
            encode_optional diagnostic.file;
            Text (if diagnostic.is_error then "error" else "warning");
            Text diagnostic.code;
            Integer diagnostic.start;
            Integer diagnostic.stop;
            Text diagnostic.message;
            Blob diagnostic.detail;
          ])
      diagnostics
  end;
  is_changed

let has_unchecked_body store ~package ~skipped_kind =
  Sql.has_row store.sql
    "SELECT 1 FROM main.body b INDEXED BY body_without_value CROSS JOIN main.definition d ON d.id \
     = b.definition WHERE b.state != 0 AND d.origin = 0 AND +d.package = ?1 AND d.kind IS NOT ?2 \
     LIMIT 1"
    [ Text package; (match skipped_kind with Some kind -> Integer kind | None -> Null) ]

let list_code_packages store ~package ~unit_kind ~target_kind ~test_kind =
  if has_unchecked_body store ~package ~skipped_kind:(Some test_kind) then None
  else
    Some
      (Sql.list_rows store.sql
         "SELECT DISTINCT e.name FROM main.definition d CROSS JOIN main.edge e ON e.source_kind = \
          ?1 AND e.source = d.id AND e.target_kind = ?2 WHERE d.package = ?3 AND d.kind != ?4 \
          ORDER BY e.name"
         [ Integer unit_kind; Integer target_kind; Text package; Integer test_kind ] (fun row ->
           Sql.read_text row 0))

let find_definition_key_anywhere store ~id =
  List.find_map
    (fun schema ->
      Sql.find_row store.sql (Printf.sprintf "SELECT key FROM %s.definition WHERE id = ?1" schema)
        [ Integer id ] (fun row -> Sql.read_blob row 0))
    ("main" :: List.map snd store.attached)

type endpoint = { kind : int; id : int; name : string }
type edge = { target : endpoint; markers : int }

let list_edges store schema ~(source : endpoint) =
  Sql.list_rows store.sql
    (Printf.sprintf
       "SELECT target_kind, target, name, markers FROM %s.edge WHERE source_kind = ?1 AND source = \
        ?2"
       (name_schema schema))
    [ Integer source.kind; Integer source.id ]
    (fun row ->
      {
        target =
          { kind = Sql.read_integer row 0; id = Sql.read_integer row 1; name = Sql.read_text row 2 };
        markers = Sql.read_integer row 3;
      })

let encode_text value =
  let buffer = Buffer.create (String.length value + 2) in
  Buffer.add_char buffer '"';
  String.iter
    (fun character ->
      match character with
      | '"' -> Buffer.add_string buffer "\\\""
      | '\\' -> Buffer.add_string buffer "\\\\"
      | character when Char.code character < 0x20 ->
          Buffer.add_string buffer (Printf.sprintf "\\u%04x" (Char.code character))
      | character -> Buffer.add_char buffer character)
    value;
  Buffer.add_char buffer '"';
  Buffer.contents buffer

let encode_integers values = "[" ^ String.concat "," (List.map string_of_int values) ^ "]"
let encode_texts values = "[" ^ String.concat "," (List.map encode_text values) ^ "]"

type edge_change = { changed : endpoint; before : int; after : int }

let replace_edges store ~(source : endpoint) edges =
  let before = Hashtbl.create 16 in
  List.iter
    (fun { target; markers } -> Hashtbl.replace before target markers)
    (list_edges store Main ~source);
  let written =
    List.filter_map
      (fun { target; markers } ->
        let markers_before = Option.value (Hashtbl.find_opt before target) ~default:0 in
        Hashtbl.remove before target;
        if markers_before = markers then None
        else Some { changed = target; before = markers_before; after = markers })
      edges
  in
  let removed =
    Hashtbl.fold
      (fun target markers removed -> { changed = target; before = markers; after = 0 } :: removed)
      before []
  in
  let encode_rows changes =
    "["
    ^ String.concat ","
        (List.map
           (fun { changed = target; after; _ } ->
             Printf.sprintf "[%d,%d,%s,%d]" target.kind target.id (encode_text target.name) after)
           changes)
    ^ "]"
  in
  if written <> [] then
    Sql.run store.sql
      "INSERT OR REPLACE INTO main.edge (source_kind, source, target_kind, target, name, markers) \
       SELECT ?1, ?2, json_extract(value, '$[0]'), json_extract(value, '$[1]'), \
       json_extract(value, '$[2]'), json_extract(value, '$[3]') FROM json_each(?3)"
      [ Integer source.kind; Integer source.id; Text (encode_rows written) ];
  if removed <> [] then
    Sql.run store.sql
      "DELETE FROM main.edge WHERE source_kind = ?1 AND source = ?2 AND (target_kind, target, \
       name) IN (SELECT json_extract(value, '$[0]'), json_extract(value, '$[1]'), \
       json_extract(value, '$[2]') FROM json_each(?3))"
      [ Integer source.kind; Integer source.id; Text (encode_rows removed) ];
  written @ removed

let has_source store ~(target : endpoint) ~source_kind ~markers =
  Sql.has_row store.sql
    "SELECT 1 FROM main.edge WHERE target_kind = ?1 AND target = ?2 AND name = ?3 AND source_kind \
     = ?4 AND (markers & ?5) != 0 LIMIT 1"
    [
      Integer target.kind; Integer target.id; Text target.name; Integer source_kind; Integer markers;
    ]

let list_sources store ~(target : endpoint) ~markers =
  Sql.list_rows store.sql
    "SELECT source_kind, source FROM main.edge WHERE target_kind = ?1 AND target = ?2 AND name = \
     ?3 AND (markers & ?4) != 0"
    [ Integer target.kind; Integer target.id; Text target.name; Integer markers ] (fun row ->
      { kind = Sql.read_integer row 0; id = Sql.read_integer row 1; name = "" })

let list_definitions_naming store ~(target : endpoint) ~markers =
  Sql.list_rows store.sql
    "SELECT DISTINCT definition.key FROM main.edge CROSS JOIN main.definition ON definition.id = \
     edge.source WHERE target_kind = ?1 AND target = ?2 AND edge.name = ?3 AND (markers & ?4) != 0 \
     ORDER BY definition.name, definition.ordinal"
    [ Integer target.kind; Integer target.id; Text target.name; Integer markers ] (fun row ->
      Sql.read_blob row 0)

let list_names_of_edges_into store ~kind ~id ~markers =
  Sql.list_rows store.sql
    "SELECT DISTINCT name FROM main.edge WHERE target_kind = ?1 AND target = ?2 AND (markers & ?3) \
     != 0 ORDER BY name" [ Integer kind; Integer id; Integer markers ] (fun row ->
      Sql.read_text row 0)

let has_unresolved store ~file =
  Sql.has_row store.sql
    "SELECT 1 FROM main.definition CROSS JOIN main.resolved ON resolved.definition = definition.id \
     WHERE definition.file = ?1 AND resolved.state != 0"
    [ Integer file ]

let mark_sources_stale store ~(target : endpoint) ~markers =
  Sql.run store.sql
    "INSERT OR IGNORE INTO main.stale (stage, id) SELECT source_kind, source FROM main.edge WHERE \
     target_kind = ?1 AND target = ?2 AND name = ?3 AND (markers & ?4) != 0"
    [ Integer target.kind; Integer target.id; Text target.name; Integer markers ]

let mark_stage_of_sources_stale store ~(target : endpoint) ~source_kind ~markers ~stage =
  Sql.run store.sql
    "INSERT OR IGNORE INTO main.stale (stage, id) SELECT ?5, source FROM main.edge WHERE \
     target_kind = ?1 AND target = ?2 AND name = ?3 AND source_kind = ?4 AND (markers & ?6) != 0"
    [
      Integer target.kind;
      Integer target.id;
      Text target.name;
      Integer source_kind;
      Integer stage;
      Integer markers;
    ]

let mark_position_holders_stale store ~(target : endpoint) ~markers ~stages =
  Sql.run store.sql
    "INSERT OR IGNORE INTO main.stale (stage, id) SELECT source_kind, source FROM main.edge WHERE \
     target_kind = ?1 AND target = ?2 AND name = ?3 AND (markers & ?4) != 0 AND (((?5 >> \
     source_kind) & 1) != 0 OR EXISTS (SELECT 1 FROM main.diagnostic WHERE stage = source_kind AND \
     unit = source))"
    [ Integer target.kind; Integer target.id; Text target.name; Integer markers; Integer stages ]

type proof_graph = { unit_kind : int; node_kind : int; markers : int }
type proof_edge = { source : int; target : int; markers : int }

let list_schema_names store = "main" :: List.map snd store.attached

let make_successor_arms store ~of_ =
  List.map
    (fun schema ->
      Printf.sprintf
        "SELECT e.target FROM %s CROSS JOIN %s.edge e ON e.source_kind = ?1 AND e.source = %s.node \
         AND e.target_kind = ?2 WHERE (e.markers & ?3) != 0"
        of_ schema of_)
    (list_schema_names store)

let make_predecessor_arms store ~of_ =
  List.map
    (fun schema ->
      Printf.sprintf
        "SELECT e.source FROM %s CROSS JOIN %s.edge e ON e.target_kind = ?2 AND e.target = %s.node \
         AND e.name = '' WHERE e.source_kind = ?1 AND (e.markers & ?3) != 0"
        of_ schema of_)
    (list_schema_names store)

let make_closure name arms =
  Printf.sprintf "%s(node) AS (SELECT value FROM json_each(?4) UNION %s)" name
    (String.concat " UNION " arms)

let bind_proof_graph graph ~seeds : cell list =
  [
    Integer graph.unit_kind;
    Integer graph.node_kind;
    Integer graph.markers;
    Text (encode_integers seeds);
  ]

let list_cycle_nodes store graph ~seeds =
  Sql.list_rows store.sql
    (Printf.sprintf
       "WITH RECURSIVE %s, %s SELECT node FROM forward INTERSECT SELECT node FROM backward"
       (make_closure "forward" (make_successor_arms store ~of_:"forward"))
       (make_closure "backward" (make_predecessor_arms store ~of_:"backward")))
    (bind_proof_graph graph ~seeds)
    (fun row -> Sql.read_integer row 0)

let list_proof_edges store graph ~nodes =
  Sql.list_rows store.sql
    (Printf.sprintf "WITH scope(node) AS (SELECT value FROM json_each(?4)) %s"
       (String.concat " UNION "
          (List.map
             (fun schema ->
               Printf.sprintf
                 "SELECT scope.node, e.target, e.markers & ?3 FROM scope CROSS JOIN %s.edge e ON \
                  e.source_kind = ?1 AND e.source = scope.node AND e.target_kind = ?2 WHERE \
                  (e.markers & ?3) != 0 AND +e.target IN (SELECT node FROM scope)"
                 schema)
             (list_schema_names store))))
    (bind_proof_graph graph ~seeds:nodes)
    (fun row ->
      {
        source = Sql.read_integer row 0;
        target = Sql.read_integer row 1;
        markers = Sql.read_integer row 2;
      })

type read_edge = { source_kind : int; source : int; target_kind : int; target : int }

let read_edge row =
  {
    source_kind = Sql.read_integer row 0;
    source = Sql.read_integer row 1;
    target_kind = Sql.read_integer row 2;
    target = Sql.read_integer row 3;
  }

let list_edges_from store schema ~source_kinds ~sources ~markers =
  Sql.list_rows store.sql
    (Printf.sprintf
       "SELECT e.source_kind, e.source, e.target_kind, e.target FROM %s.edge e WHERE e.source_kind \
        IN (SELECT value FROM json_each(?1)) AND e.source IN (SELECT value FROM json_each(?2)) AND \
        (e.markers & ?3) != 0"
       (name_schema schema))
    [ Text (encode_integers source_kinds); Text (encode_integers sources); Integer markers ]
    read_edge

let list_edges_into store ~target_kinds ~targets ~markers =
  Sql.list_rows store.sql
    "SELECT e.source_kind, e.source, e.target_kind, e.target FROM main.edge e WHERE e.target_kind \
     IN (SELECT value FROM json_each(?1)) AND e.target IN (SELECT value FROM json_each(?2)) AND \
     (e.markers & ?3) != 0"
    [ Text (encode_integers target_kinds); Text (encode_integers targets); Integer markers ]
    read_edge

let list_definitions_identified store ~ids =
  List.concat_map
    (fun schema ->
      Sql.list_rows store.sql
        (Printf.sprintf
           "SELECT id, path, key FROM %s.definition WHERE id IN (SELECT value FROM json_each(?1)) \
            UNION SELECT id, path, key FROM %s.definition WHERE ordinal = 0 AND path IN (SELECT \
            value FROM json_each(?1))"
           schema schema)
        [ Text (encode_integers ids) ]
        (fun row -> (Sql.read_integer row 0, Sql.read_integer row 1, Sql.read_blob row 2)))
    (list_schema_names store)

let mark_paths_stale store ~stage ~paths =
  Sql.run store.sql
    "INSERT OR IGNORE INTO main.stale (stage, id) SELECT DISTINCT ?1, path FROM main.definition \
     WHERE path IN (SELECT value FROM json_each(?2))"
    [ Integer stage; Text (encode_integers paths) ]

let list_keys_of_paths store ~paths =
  List.concat_map
    (fun schema ->
      Sql.list_rows store.sql
        (Printf.sprintf
           "SELECT path, key FROM %s.definition WHERE ordinal = 0 AND path IN (SELECT value FROM \
            json_each(?1))"
           schema)
        [ Text (encode_integers paths) ]
        (fun row -> (Sql.read_integer row 0, Sql.read_blob row 1)))
    (list_schema_names store)

let mark_groups_stale store ~stage ~path =
  List.iter
    (fun table ->
      Sql.run store.sql
        (Printf.sprintf
           "INSERT OR IGNORE INTO main.stale (stage, id) SELECT ?1, path FROM main.%s WHERE \
            representative = (SELECT representative FROM main.%s WHERE path = ?2)"
           table table)
        [ Integer stage; Integer path ])
    [ "recursion_group"; "proof_group" ]

type item = { id : int; key : string; label : string; definition : int option }

let insert_item store (item : item) =
  Sql.run store.sql
    "INSERT OR IGNORE INTO main.item (id, definition, key, label) VALUES (?1, ?2, ?3, ?4)"
    [ Integer item.id; encode_optional item.definition; Blob item.key; Text item.label ];
  Sql.count_changes store.sql > 0

let find_item_key store ~id =
  Sql.find_row store.sql "SELECT key FROM main.item WHERE id = ?1" [ Integer id ] (fun row ->
      Sql.read_blob row 0)

let list_item_keys store =
  Sql.list_rows store.sql "SELECT key FROM main.item" [] (fun row -> Sql.read_blob row 0)

let remove_item store ~id = Sql.run store.sql "DELETE FROM main.item WHERE id = ?1" [ Integer id ]

type item_graph = {
  lower_kind : int;
  evaluate_kind : int;
  item_kind : int;
  references : int;
  claims : int;
  claim_kinds : int list;
}

let mark_items_stale store ~stage =
  Sql.run store.sql "INSERT OR IGNORE INTO main.stale (stage, id) SELECT ?1, id FROM main.item"
    [ Integer stage ]

type linked = {
  linked_id : int;
  linked_key : string;
  sites : string option;
  text_hash : string option;
  is_unevaluated : bool;
  is_unit_stale : bool;
}

let list_linked store graph ~profile ~unit_kind ~roots =
  Sql.list_rows store.sql
    "WITH RECURSIVE down(node) AS (SELECT value FROM json_each(?4) UNION SELECT e.target FROM down \
     CROSS JOIN main.lowered l ON l.item = down.node CROSS JOIN main.edge e ON e.source_kind = \
     CASE WHEN l.is_evaluated = 1 THEN ?6 ELSE ?2 END AND e.source = down.node AND e.target_kind = \
     ?1 WHERE (e.markers & ?3) != 0) SELECT down.node, i.key, l.sites, u.state, u.text_hash, \
     l.is_evaluated = 1 AND EXISTS (SELECT 1 FROM main.stale s WHERE s.stage = ?6 AND s.id = \
     down.node), EXISTS (SELECT 1 FROM main.stale s WHERE s.stage = ?7 AND s.id = down.node) FROM \
     down CROSS JOIN main.item i ON i.id = down.node LEFT JOIN main.lowered l ON l.item = \
     down.node LEFT JOIN main.unit u ON u.item = down.node AND u.profile = ?5"
    [
      Integer graph.item_kind;
      Integer graph.lower_kind;
      Integer graph.references;
      Text (encode_integers roots);
      Integer profile;
      Integer graph.evaluate_kind;
      Integer unit_kind;
    ]
    (fun row ->
      {
        linked_id = Sql.read_integer row 0;
        linked_key = Sql.read_blob row 1;
        sites = (if Sql.is_null row 2 then None else Some (Sql.read_blob row 2));
        text_hash =
          (if Sql.is_null row 3 || Sql.read_integer row 3 <> 0 then None
           else Some (Sql.read_blob row 4));
        is_unevaluated = (not (Sql.is_null row 5)) && Sql.read_integer row 5 = 1;
        is_unit_stale = Sql.read_integer row 6 = 1;
      })

type claim_edges = Every_edge | Settled_edges of { packages : string list option }

let require_settled ~stage ~unit =
  Printf.sprintf " AND NOT EXISTS (SELECT 1 FROM main.stale s WHERE s.stage = %s AND s.id = %s)"
    stage unit

let select_claim_kinds graph =
  Printf.sprintf " AND c.source_kind IN (%s)"
    (String.concat ", " (List.map string_of_int graph.claim_kinds))

let select_settled_claims ~packages ~parameter =
  let condition = require_settled ~stage:"c.source_kind" ~unit:"c.source" in
  match packages with
  | None -> ("", condition, [])
  | Some packages ->
      ( " CROSS JOIN main.definition d ON d.id = c.source",
        Printf.sprintf "%s AND +d.package IN (SELECT value FROM json_each(?%d))" condition parameter,
        [ Text (encode_texts packages) ] )

let is_item_claimed store graph ~item ~over =
  let reference_condition, claimant, claim_condition, packages =
    match over with
    | Every_edge -> ("", "", "", [])
    | Settled_edges { packages } ->
        let claimant, claim_condition, packages = select_settled_claims ~packages ~parameter:4 in
        (require_settled ~stage:"?3" ~unit:"e.source", claimant, claim_condition, packages)
  in
  let has_claim node =
    Sql.has_row store.sql
      (Printf.sprintf
         "SELECT 1 FROM main.edge c%s WHERE c.target_kind = ?1 AND c.target = ?2 AND c.name = ''%s \
          AND (c.markers & ?3) != 0%s LIMIT 1"
         claimant (select_claim_kinds graph) claim_condition)
      ([ Integer graph.item_kind; Integer node; Integer graph.claims ] @ packages)
  in
  let find_referrer node ~from =
    Sql.find_row store.sql
      (Printf.sprintf
         "SELECT e.source FROM main.edge e WHERE e.target_kind = ?1 AND e.target = ?2 AND e.name = \
          '' AND e.source_kind = ?3 AND e.source >= ?4 AND (e.markers & ?5) != 0%s ORDER BY \
          e.source LIMIT 1"
         reference_condition)
      [
        Integer graph.item_kind;
        Integer node;
        Integer graph.lower_kind;
        Integer from;
        Integer graph.references;
      ] (fun row -> Sql.read_integer row 0)
  in
  let visited = Hashtbl.create 16 in
  let rec search = function
    | [] -> false
    | (node, from) :: pending -> (
        match find_referrer node ~from with
        | None -> search pending
        | Some referrer ->
            let pending = if referrer = max_int then pending else (node, referrer + 1) :: pending in
            if Hashtbl.mem visited referrer then search pending
            else begin
              Hashtbl.replace visited referrer ();
              has_claim referrer || search ((referrer, min_int) :: pending)
            end)
  in
  Hashtbl.replace visited item ();
  has_claim item || search [ (item, min_int) ]

let list_claimed_among store graph ~items ~packages =
  let claimant, claim_condition, packages = select_settled_claims ~packages ~parameter:4 in
  Sql.list_rows store.sql
    (Printf.sprintf
       "SELECT DISTINCT c.target FROM json_each(?1) i CROSS JOIN main.edge c ON c.target_kind = ?2 \
        AND c.target = i.value AND c.name = ''%s%s WHERE (c.markers & ?3) != 0%s"
       (select_claim_kinds graph) claimant claim_condition)
    ([ Text (encode_integers items); Integer graph.item_kind; Integer graph.claims ] @ packages)
    (fun row -> Sql.read_integer row 0)

let merge paths ~into =
  let merged = create_memory () in
  Fun.protect
    ~finally:(fun () -> Sql.close merged.sql)
    (fun () ->
      List.iter
        (fun path ->
          let source = name_schema (attach merged path) in
          List.iter
            (fun table ->
              if table <> "meta" then
                Sql.run merged.sql
                  (Printf.sprintf "INSERT OR IGNORE INTO main.\"%s\" SELECT * FROM %s.\"%s\"" table
                     source table)
                  [])
            (Schema.list_table_names ());
          detach merged path)
        paths;
      save merged ~into)

type located = { stage : int; base : int option; is_in_test : bool; detail : string }

let list_file_diagnostics store schema ~file ~test_kind =
  let schema = name_schema schema in
  Sql.list_rows store.sql
    (Printf.sprintf
       "SELECT d.stage, def.base, def.kind = ?2, d.detail FROM %s.definition def CROSS JOIN \
        %s.diagnostic d ON d.definition = def.id WHERE def.file = ?1 UNION ALL SELECT d.stage, \
        NULL, 0, d.detail FROM %s.diagnostic d WHERE d.file = ?1"
       schema schema schema) [ Integer file; Integer test_kind ] (fun row ->
      {
        stage = Sql.read_integer row 0;
        base = (if Sql.is_null row 1 then None else Some (Sql.read_integer row 1));
        is_in_test = Sql.read_integer row 2 <> 0;
        detail = Sql.read_blob row 3;
      })

let has_error store ~package ~last_stage ~hidden_stage =
  Sql.has_row store.sql
    "SELECT 1 FROM main.diagnostic WHERE package = ?1 AND severity = 'error' AND stage <= ?2 AND \
     stage IS NOT ?3 LIMIT 1"
    [ Text package; Integer last_stage; encode_optional hidden_stage ]

type scope = Everything | Packages of string list | Files of int list

let find_unproven_definition store ~scope ~origin =
  let membership, members =
    match scope with
    | Everything -> ("", [])
    | Packages packages ->
        (" AND +d.package IN (SELECT value FROM json_each(?2))", [ Text (encode_texts packages) ])
    | Files files ->
        (" AND +d.file IN (SELECT value FROM json_each(?2))", [ Text (encode_integers files) ])
  in
  Sql.find_row store.sql
    (Printf.sprintf
       "SELECT d.key FROM main.proof p INDEXED BY proof_without_value CROSS JOIN main.definition d \
        ON d.id = p.definition WHERE p.state != 0 AND d.origin = ?1%s LIMIT 1"
       membership) (Integer origin :: members) (fun row -> Sql.read_blob row 0)

type hole = { home : int; start : int; stop : int }

let list_holes store schema ~definition =
  Sql.list_rows store.sql
    (Printf.sprintf "SELECT home, start, stop FROM %s.hole WHERE definition = ?1 ORDER BY position"
       (name_schema schema))
    [ Integer definition ]
    (fun row ->
      {
        home = Sql.read_integer row 0;
        start = Sql.read_integer row 1;
        stop = Sql.read_integer row 2;
      })

let replace_holes store ~definition holes =
  if list_holes store Main ~definition <> holes then begin
    Sql.run store.sql "DELETE FROM main.hole WHERE definition = ?1" [ Integer definition ];
    List.iteri
      (fun position (hole : hole) ->
        Sql.run store.sql
          "INSERT INTO main.hole (definition, position, home, start, stop) VALUES (?1, ?2, ?3, ?4, \
           ?5)"
          [
            Integer definition;
            Integer position;
            Integer hole.home;
            Integer hole.start;
            Integer hole.stop;
          ])
      holes
  end

type citation = { cited : int; clause_start : int; clause_stop : int }

type verdict = {
  code : string;
  start : int;
  stop : int;
  shows : string;
  is_proven : bool;
  trusts_compiled_code : bool;
  failure : string option;
  citation : citation option;
}

let verdict_columns =
  "v.code, v.start, v.stop, v.shows, v.proven, v.trusts_compiled_code, v.failure, v.cited, \
   v.cited_start, v.cited_stop"

let read_verdict row ~first =
  {
    code = Sql.read_text row first;
    start = Sql.read_integer row (first + 1);
    stop = Sql.read_integer row (first + 2);
    shows = Sql.read_text row (first + 3);
    is_proven = Sql.read_integer row (first + 4) <> 0;
    trusts_compiled_code = Sql.read_integer row (first + 5) <> 0;
    failure = (if Sql.is_null row (first + 6) then None else Some (Sql.read_blob row (first + 6)));
    citation =
      (if Sql.is_null row (first + 7) then None
       else
         Some
           {
             cited = Sql.read_integer row (first + 7);
             clause_start = Sql.read_integer row (first + 8);
             clause_stop = Sql.read_integer row (first + 9);
           });
  }

let list_verdicts store ~definition =
  Sql.list_rows store.sql
    (Printf.sprintf "SELECT %s FROM main.verdict v WHERE v.definition = ?1 ORDER BY v.position"
       verdict_columns)
    [ Integer definition ] (read_verdict ~first:0)

let list_file_verdicts store ~file =
  Sql.list_rows store.sql
    (Printf.sprintf
       "SELECT d.base, %s FROM main.definition d CROSS JOIN main.verdict v ON v.definition = d.id \
        WHERE d.file = ?1 ORDER BY d.base + v.start, d.base + v.stop, v.code, v.position"
       verdict_columns) [ Integer file ] (fun row ->
      (Sql.read_integer row 0, read_verdict row ~first:1))

let replace_verdicts store ~definition verdicts =
  let is_changed = list_verdicts store ~definition <> verdicts in
  if is_changed then begin
    Sql.run store.sql "DELETE FROM main.verdict WHERE definition = ?1" [ Integer definition ];
    List.iteri
      (fun position (verdict : verdict) ->
        Sql.run store.sql
          "INSERT INTO main.verdict (definition, position, code, start, stop, shows, proven, \
           trusts_compiled_code, failure, cited, cited_start, cited_stop) VALUES (?1, ?2, ?3, ?4, \
           ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12)"
          [
            Integer definition;
            Integer position;
            Text verdict.code;
            Integer verdict.start;
            Integer verdict.stop;
            Text verdict.shows;
            Integer (Bool.to_int verdict.is_proven);
            Integer (Bool.to_int verdict.trusts_compiled_code);
            (match verdict.failure with Some failure -> Blob failure | None -> Null);
            encode_optional (Option.map (fun citation -> citation.cited) verdict.citation);
            encode_optional (Option.map (fun citation -> citation.clause_start) verdict.citation);
            encode_optional (Option.map (fun citation -> citation.clause_stop) verdict.citation);
          ])
      verdicts
  end;
  is_changed

let list_differing_rows store ~table ~columns ~before ~after =
  let select ~of_ ~minus =
    Printf.sprintf "SELECT %s FROM (SELECT * FROM %s.\"%s\"%s)"
      (String.concat ", " (List.map (Printf.sprintf "\"%s\"") columns))
      (name_schema of_) table
      (match minus with
      | Some minus -> Printf.sprintf " EXCEPT SELECT * FROM %s.\"%s\"" (name_schema minus) table
      | None -> "")
  in
  match
    match (before, after) with
    | Some before, Some after ->
        [ select ~of_:before ~minus:(Some after); select ~of_:after ~minus:(Some before) ]
    | Some only, None | None, Some only -> [ select ~of_:only ~minus:None ]
    | None, None -> []
  with
  | [] -> []
  | sides ->
      Sql.list_rows store.sql (String.concat " UNION " sides) [] (read_cells (List.length columns))

let mark_readers_of_targets store ~(targets : endpoint list) ~markers =
  if targets <> [] then
    Sql.run store.sql
      "INSERT OR IGNORE INTO main.stale (stage, id) SELECT e.source_kind, e.source FROM \
       json_each(?1) changed CROSS JOIN main.edge e WHERE e.target_kind = \
       json_extract(changed.value, '$[0]') AND e.target = json_extract(changed.value, '$[1]') AND \
       e.name = json_extract(changed.value, '$[2]') AND (e.markers & ?2) != 0"
      [
        Text
          ("["
          ^ String.concat ","
              (List.map
                 (fun (target : endpoint) ->
                   Printf.sprintf "[%d,%d,%s]" target.kind target.id (encode_text target.name))
                 targets)
          ^ "]");
        Integer markers;
      ]

let list_unread store ~table ~id_column ~section ~target_kinds =
  Sql.list_rows store.sql
    (Printf.sprintf
       "SELECT DISTINCT d.name FROM main.\"%s\" f CROSS JOIN main.definition d ON d.\"%s\" = \
        f.\"%s\" WHERE f.state = 0%s AND NOT EXISTS (SELECT 1 FROM main.edge e WHERE e.target_kind \
        IN (SELECT value FROM json_each(?1)) AND e.target = f.\"%s\") ORDER BY d.name"
       table
       (if id_column = "path" then "path" else "id")
       id_column
       (match section with
       | Some section -> Printf.sprintf " AND f.section = %d" section
       | None -> "")
       id_column)
    [ Text (encode_integers target_kinds) ]
    (fun row -> Sql.read_text row 0)

let count_differing_rows store ~other =
  List.filter_map
    (fun table ->
      if table = "meta" then None
      else
        let count ~of_ ~minus =
          Option.value ~default:0
            (Sql.find_row store.sql
               (Printf.sprintf
                  "SELECT COUNT(*) FROM (SELECT * FROM %s.\"%s\" EXCEPT SELECT * FROM %s.\"%s\")"
                  of_ table minus table) [] (fun row -> Sql.read_integer row 0))
        in
        let other = name_schema other in
        match count ~of_:"main" ~minus:other + count ~of_:other ~minus:"main" with
        | 0 -> None
        | differing -> Some (table, differing))
    (Schema.list_table_names ())

let keep_for_dependents store ~markers =
  Sql.run store.sql "UPDATE main.edge SET markers = markers & ?1" [ Integer markers ];
  Sql.run store.sql "DELETE FROM main.edge WHERE markers = 0" [];
  Sql.run store.sql "DELETE FROM main.stale" [];
  Sql.run store.sql "DELETE FROM main.item" []

let mark_stale store ~stage ~id =
  Sql.run store.sql "INSERT OR IGNORE INTO main.stale (stage, id) VALUES (?1, ?2)"
    [ Integer stage; Integer id ]

let unmark_stale store ~stage ~id =
  Sql.run store.sql "DELETE FROM main.stale WHERE stage = ?1 AND id = ?2"
    [ Integer stage; Integer id ];
  Sql.count_changes store.sql > 0

type unit_entity =
  | File_unit
  | Module_unit
  | Definition_unit
  | Path_unit
  | Dependency_unit
  | Item_unit

let list_stale store ~stage ~entity ~scope =
  let table, id_column =
    match entity with
    | File_unit -> ("file", "id")
    | Module_unit -> ("module", "id")
    | Definition_unit -> ("definition", "id")
    | Path_unit -> ("definition", "path")
    | Dependency_unit -> ("dependency", "id")
    | Item_unit -> ("item", "id")
  in
  let list_joined ~from_ column members =
    Sql.list_rows store.sql
      (Printf.sprintf
         "SELECT DISTINCT s.id FROM %s WHERE s.stage = ?1 AND e.\"%s\" = s.id AND e.\"%s\" IN \
          (SELECT value FROM json_each(?2))"
         (Printf.sprintf from_ table) id_column column)
      [ Integer stage; Text members ]
      (fun row -> Sql.read_integer row 0)
  in
  let list_stale_among = list_joined ~from_:"main.stale s CROSS JOIN main.\"%s\" e" in
  let list_among = list_joined ~from_:"main.\"%s\" e CROSS JOIN main.stale s" in
  match (scope, entity) with
  | Everything, _ ->
      Sql.list_rows store.sql "SELECT id FROM main.stale WHERE stage = ?1" [ Integer stage ]
        (fun row -> Sql.read_integer row 0)
  | Packages packages, (File_unit | Module_unit | Definition_unit | Path_unit | Dependency_unit) ->
      list_stale_among "package" (encode_texts packages)
  | Files files, (Definition_unit | Path_unit) -> list_among "file" (encode_integers files)
  | Files files, File_unit -> list_among "id" (encode_integers files)
  | (Packages _ | Files _), Item_unit -> []
  | Files _, (Module_unit | Dependency_unit) -> []

type entry = {
  file : int;
  position : int;
  module_ : int;
  file_name : string;
  name : string;
  kind : int;
  visibility : int;
  is_generic : bool;
}

let entry_columns = "file, position, module, file_name, name, kind, visibility, is_generic"

let read_entry row =
  {
    file = Sql.read_integer row 0;
    position = Sql.read_integer row 1;
    module_ = Sql.read_integer row 2;
    file_name = Sql.read_text row 3;
    name = Sql.read_text row 4;
    kind = Sql.read_integer row 5;
    visibility = Sql.read_integer row 6;
    is_generic = Sql.read_integer row 7 <> 0;
  }

let list_file_entries store ~file =
  Sql.list_rows store.sql
    (Printf.sprintf "SELECT %s FROM main.entry WHERE file = ?1 ORDER BY position" entry_columns)
    [ Integer file ] read_entry

let replace_file_entries store ~file entries =
  Sql.run store.sql "DELETE FROM main.entry WHERE file = ?1" [ Integer file ];
  List.iter
    (fun (entry : entry) ->
      Sql.run store.sql
        (Printf.sprintf "INSERT INTO main.entry (%s) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8)"
           entry_columns)
        [
          Integer entry.file;
          Integer entry.position;
          Integer entry.module_;
          Text entry.file_name;
          Text entry.name;
          Integer entry.kind;
          Integer entry.visibility;
          Integer (Bool.to_int entry.is_generic);
        ])
    entries

let find_entry store schema ~module_ ~name =
  Sql.find_row store.sql
    (Printf.sprintf
       "SELECT %s FROM %s.entry WHERE module = ?1 AND name = ?2 ORDER BY file_name, position LIMIT \
        1"
       entry_columns (name_schema schema))
    [ Integer module_; Text name ] read_entry

let list_module_entries store schema ~module_ =
  Sql.list_rows store.sql
    (Printf.sprintf "SELECT %s FROM %s.entry WHERE module = ?1 ORDER BY file_name, position"
       entry_columns (name_schema schema))
    [ Integer module_ ] read_entry

type definition = {
  id : int;
  key : string;
  package : string;
  module_ : int;
  path : int;
  ordinal : int;
  name : string;
  owner : int option;
  member : string option;
  kind : int;
  visibility : int;
  is_generic : bool;
  origin : int;
  supplied_from : int option;
  container : int option;
  file : int option;
  position : int option;
  base : int option;
  stop : int option;
  text_hash : int option;
}

type selection =
  | Of_module of int
  | Of_file of int
  | Of_package of string
  | Of_container of int
  | Of_path of int

let definition_columns =
  "id, key, package, module, path, ordinal, name, owner, member, kind, visibility, is_generic, \
   origin, supplied_from, container, file, position, base, stop, text_hash"

let read_optional_integer row index =
  if Sql.is_null row index then None else Some (Sql.read_integer row index)

let bind_optional_integer = function Some value -> Integer value | None -> Null

let read_definition row =
  {
    id = Sql.read_integer row 0;
    key = Sql.read_blob row 1;
    package = Sql.read_text row 2;
    module_ = Sql.read_integer row 3;
    path = Sql.read_integer row 4;
    ordinal = Sql.read_integer row 5;
    name = Sql.read_text row 6;
    owner = read_optional_integer row 7;
    member = (if Sql.is_null row 8 then None else Some (Sql.read_text row 8));
    kind = Sql.read_integer row 9;
    visibility = Sql.read_integer row 10;
    is_generic = Sql.read_integer row 11 <> 0;
    origin = Sql.read_integer row 12;
    supplied_from = read_optional_integer row 13;
    container = read_optional_integer row 14;
    file = read_optional_integer row 15;
    position = read_optional_integer row 16;
    base = read_optional_integer row 17;
    stop = read_optional_integer row 18;
    text_hash = read_optional_integer row 19;
  }

let find_definition store schema ~id =
  Sql.find_row store.sql
    (Printf.sprintf "SELECT %s FROM %s.definition WHERE id = ?1" definition_columns
       (name_schema schema))
    [ Integer id ] read_definition

let list_definitions store schema selection =
  let condition, arguments =
    match selection with
    | Of_module module_ -> ("module = ?1", [ Integer module_ ])
    | Of_file file -> ("file = ?1 ORDER BY position", [ Integer file ])
    | Of_package package -> ("package = ?1", [ Text package ])
    | Of_container container -> ("container = ?1 ORDER BY position", [ Integer container ])
    | Of_path path -> ("path = ?1", [ Integer path ])
  in
  Sql.list_rows store.sql
    (Printf.sprintf "SELECT %s FROM %s.definition WHERE %s" definition_columns (name_schema schema)
       condition)
    arguments read_definition

let qualified_definition_columns =
  String.concat ", "
    (List.map
       (fun column -> "d." ^ String.trim column)
       (String.split_on_char ',' definition_columns))

let find_source_definition store ~(target : endpoint) ~source_kind ~markers ~from_ =
  Sql.find_row store.sql
    (Printf.sprintf
       "SELECT %s FROM main.edge e CROSS JOIN main.definition d ON d.id = e.source WHERE \
        e.target_kind = ?1 AND e.target = ?2 AND e.name = ?3 AND e.source_kind = ?4 AND e.source \
        >= ?5 AND (e.markers & ?6) != 0 ORDER BY e.source LIMIT 1"
       qualified_definition_columns)
    [
      Integer target.kind;
      Integer target.id;
      Text target.name;
      Integer source_kind;
      Integer from_;
      Integer markers;
    ]
    read_definition

let list_target_definitions store ~(source : endpoint) ~target_kind ~markers ~origin =
  Sql.list_rows store.sql
    (Printf.sprintf
       "SELECT %s, e.markers FROM main.edge e CROSS JOIN main.definition d ON d.path = e.target \
        WHERE e.source_kind = ?1 AND e.source = ?2 AND e.target_kind = ?3 AND (e.markers & ?4) != \
        0 AND d.origin = ?5 AND d.ordinal = 0 ORDER BY e.target"
       qualified_definition_columns)
    [ Integer source.kind; Integer source.id; Integer target_kind; Integer markers; Integer origin ]
    (fun row -> (read_definition row, Sql.read_integer row 20))

let list_package_member_keys store schema ~package ~member ~kind ~origin =
  Sql.list_rows store.sql
    (Printf.sprintf
       "SELECT key FROM %s.definition WHERE package = ?1 AND member = ?2 AND kind = ?3 AND origin \
        = ?4 AND ordinal = 0"
       (name_schema schema))
    [ Text package; Text member; Integer kind; Integer origin ]
    (fun row -> Sql.read_blob row 0)

let replace_definition store (definition : definition) =
  Sql.run store.sql
    (Printf.sprintf
       "INSERT OR REPLACE INTO main.definition (%s) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, \
        ?10, ?11, ?12, ?13, ?14, ?15, ?16, ?17, ?18, ?19, ?20)"
       definition_columns)
    [
      Integer definition.id;
      Blob definition.key;
      Text definition.package;
      Integer definition.module_;
      Integer definition.path;
      Integer definition.ordinal;
      Text definition.name;
      bind_optional_integer definition.owner;
      (match definition.member with Some member -> Text member | None -> Null);
      Integer definition.kind;
      Integer definition.visibility;
      Integer (Bool.to_int definition.is_generic);
      Integer definition.origin;
      bind_optional_integer definition.supplied_from;
      bind_optional_integer definition.container;
      bind_optional_integer definition.file;
      bind_optional_integer definition.position;
      bind_optional_integer definition.base;
      bind_optional_integer definition.stop;
      bind_optional_integer definition.text_hash;
    ]

let remove_definition store ~id =
  Sql.run store.sql "DELETE FROM main.definition WHERE id = ?1" [ Integer id ];
  Sql.run store.sql "DELETE FROM main.syntax WHERE definition = ?1" [ Integer id ]

type syntax = { tree : string; spans : string; syntax_errors : string }

let find_syntax store schema ~definition =
  Sql.find_row store.sql
    (Printf.sprintf "SELECT tree, spans, syntax_errors FROM %s.syntax WHERE definition = ?1"
       (name_schema schema))
    [ Integer definition ]
    (fun row ->
      {
        tree = Sql.read_blob row 0;
        spans = Sql.read_blob row 1;
        syntax_errors = Sql.read_blob row 2;
      })

let find_syntax_column store schema ~definition ~column =
  Sql.find_row store.sql
    (Printf.sprintf "SELECT %s FROM %s.syntax WHERE definition = ?1" column (name_schema schema))
    [ Integer definition ]
    (fun row -> Sql.read_blob row 0)

let find_tree store schema ~definition = find_syntax_column store schema ~definition ~column:"tree"

let find_spans store schema ~definition =
  find_syntax_column store schema ~definition ~column:"spans"

let find_syntax_errors store schema ~definition =
  find_syntax_column store schema ~definition ~column:"syntax_errors"

let replace_syntax store ~definition { tree; spans; syntax_errors } =
  Sql.run store.sql
    "INSERT OR REPLACE INTO main.syntax (definition, tree, spans, syntax_errors) VALUES (?1, ?2, \
     ?3, ?4)"
    [ Integer definition; Blob tree; Blob spans; Blob syntax_errors ]

type dependency = { id : int; package : string; dependency : string; capabilities : string }

let replace_package store ~name ~id ~dependencies =
  Sql.run store.sql "INSERT OR REPLACE INTO main.package (name, id) VALUES (?1, ?2)"
    [ Text name; Integer id ];
  Sql.run store.sql "DELETE FROM main.dependency WHERE package = ?1" [ Text name ];
  List.iteri
    (fun position (dependency : dependency) ->
      Sql.run store.sql
        "INSERT INTO main.dependency (id, package, position, dependency, capabilities) VALUES (?1, \
         ?2, ?3, ?4, ?5)"
        [
          Integer dependency.id;
          Text name;
          Integer position;
          Text dependency.dependency;
          Blob dependency.capabilities;
        ])
    dependencies

let remove_package store ~name =
  Sql.run store.sql "DELETE FROM main.package WHERE name = ?1" [ Text name ];
  Sql.run store.sql "DELETE FROM main.dependency WHERE package = ?1" [ Text name ]

let list_packages store schema =
  Sql.list_rows store.sql
    (Printf.sprintf "SELECT name FROM %s.package ORDER BY name" (name_schema schema))
    []
    (fun row -> Sql.read_text row 0)

let read_dependency row =
  {
    id = Sql.read_integer row 0;
    package = Sql.read_text row 1;
    dependency = Sql.read_text row 2;
    capabilities = Sql.read_blob row 3;
  }

let list_dependencies store schema ~package =
  Sql.list_rows store.sql
    (Printf.sprintf
       "SELECT id, package, dependency, capabilities FROM %s.dependency WHERE package = ?1 ORDER \
        BY position"
       (name_schema schema))
    [ Text package ] read_dependency

let find_dependency store ~id =
  Sql.find_row store.sql
    "SELECT id, package, dependency, capabilities FROM main.dependency WHERE id = ?1" [ Integer id ]
    read_dependency

type file = {
  id : int;
  package : string;
  module_ : int;
  name : string;
  key : string;
  text : string;
}

let read_file row =
  {
    id = Sql.read_integer row 0;
    package = Sql.read_text row 1;
    module_ = Sql.read_integer row 2;
    name = Sql.read_text row 3;
    key = Sql.read_blob row 4;
    text = Sql.read_blob row 5;
  }

let find_file store schema ~id =
  Sql.find_row store.sql
    (Printf.sprintf "SELECT id, package, module, name, key, text FROM %s.file WHERE id = ?1"
       (name_schema schema))
    [ Integer id ] read_file

let list_files store schema selection =
  let condition, arguments =
    match selection with
    | Of_module module_ -> ("module = ?1", [ Integer module_ ])
    | Of_package package -> ("package = ?1", [ Text package ])
    | Of_file _ | Of_container _ | Of_path _ ->
        raise (Sql.Failed "files are selected by module or by package")
  in
  Sql.list_rows store.sql
    (Printf.sprintf
       "SELECT id, package, module, name, key, text FROM %s.file WHERE %s ORDER BY name"
       (name_schema schema) condition)
    arguments read_file

let replace_file store (file : file) =
  Sql.run store.sql
    "INSERT OR REPLACE INTO main.file (id, package, module, name, key, text) VALUES (?1, ?2, ?3, \
     ?4, ?5, ?6)"
    [
      Integer file.id;
      Text file.package;
      Integer file.module_;
      Text file.name;
      Blob file.key;
      Blob file.text;
    ]

let remove_file store ~id = Sql.run store.sql "DELETE FROM main.file WHERE id = ?1" [ Integer id ]

let list_imports store schema ~file =
  Sql.list_rows store.sql
    (Printf.sprintf "SELECT name, module FROM %s.import WHERE file = ?1 ORDER BY position"
       (name_schema schema))
    [ Integer file ]
    (fun row -> (Sql.read_text row 0, Sql.read_blob row 1))

let replace_imports store ~file imports =
  Sql.run store.sql "DELETE FROM main.import WHERE file = ?1" [ Integer file ];
  List.iteri
    (fun position (name, module_) ->
      Sql.run store.sql
        "INSERT INTO main.import (file, position, name, module) VALUES (?1, ?2, ?3, ?4)"
        [ Integer file; Integer position; Text name; Blob module_ ])
    imports

type impl = {
  definition : int;
  module_ : int;
  position : int;
  trait : int;
  type_ : int;
  entry : string;
}

type impl_selection = Impls_of_trait of int | Impls_of_type of int | Impls_of_module of int

let list_impls store schema ~package selection =
  let condition, arguments =
    match selection with
    | Impls_of_trait trait -> ("package = ?1 AND trait = ?2", [ Text package; Integer trait ])
    | Impls_of_type type_ -> ("package = ?1 AND type = ?2", [ Text package; Integer type_ ])
    | Impls_of_module module_ -> ("package = ?1 AND module = ?2", [ Text package; Integer module_ ])
  in
  Sql.list_rows store.sql
    (Printf.sprintf "SELECT definition, module, position, trait, type, entry FROM %s.impl WHERE %s"
       (name_schema schema) condition)
    arguments
    (fun row ->
      {
        definition = Sql.read_integer row 0;
        module_ = Sql.read_integer row 1;
        position = Sql.read_integer row 2;
        trait = Sql.read_integer row 3;
        type_ = Sql.read_integer row 4;
        entry = Sql.read_blob row 5;
      })

let replace_module_impls store ~package ~module_ impls =
  Sql.run store.sql "DELETE FROM main.impl WHERE module = ?1" [ Integer module_ ];
  List.iter
    (fun (impl : impl) ->
      Sql.run store.sql
        "INSERT OR REPLACE INTO main.impl (definition, package, module, position, trait, type, \
         entry) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7)"
        [
          Integer impl.definition;
          Text package;
          Integer impl.module_;
          Integer impl.position;
          Integer impl.trait;
          Integer impl.type_;
          Blob impl.entry;
        ])
    impls

type law_proof = { definition : int; module_ : int; trait : int; law : string; type_ : int }

let list_law_proofs store schema ~package ~trait ~law ~type_ =
  Sql.list_rows store.sql
    (Printf.sprintf
       "SELECT definition FROM %s.law_proof WHERE package = ?1 AND trait = ?2 AND law = ?3 AND \
        type = ?4"
       (name_schema schema))
    [ Text package; Integer trait; Text law; Integer type_ ]
    (fun row -> Sql.read_integer row 0)

let replace_module_law_proofs store ~package ~module_ law_proofs =
  let before =
    Sql.list_rows store.sql
      "SELECT definition, trait, law, type FROM main.law_proof WHERE module = ?1"
      [ Integer module_ ] (fun row ->
        {
          definition = Sql.read_integer row 0;
          module_;
          trait = Sql.read_integer row 1;
          law = Sql.read_text row 2;
          type_ = Sql.read_integer row 3;
        })
  in
  let list_missing_from others rows = List.filter (fun row -> not (List.mem row others)) rows in
  match list_missing_from law_proofs before @ list_missing_from before law_proofs with
  | [] -> []
  | differing ->
      Sql.run store.sql "DELETE FROM main.law_proof WHERE module = ?1" [ Integer module_ ];
      List.iter
        (fun (law_proof : law_proof) ->
          Sql.run store.sql
            "INSERT OR REPLACE INTO main.law_proof (definition, package, module, trait, law, type) \
             VALUES (?1, ?2, ?3, ?4, ?5, ?6)"
            [
              Integer law_proof.definition;
              Text package;
              Integer law_proof.module_;
              Integer law_proof.trait;
              Text law_proof.law;
              Integer law_proof.type_;
            ])
        law_proofs;
      differing

let has_module store schema ~module_ =
  let schema = name_schema schema in
  Sql.has_row store.sql
    (Printf.sprintf
       "SELECT 1 FROM %s.file WHERE module = ?1 UNION ALL SELECT 1 FROM %s.entry WHERE module = ?1 \
        LIMIT 1"
       schema schema)
    [ Integer module_ ]

let find_place store schema ~definition =
  let schema = name_schema schema in
  Sql.find_row store.sql
    (Printf.sprintf
       "SELECT file.key, definition.base FROM %s.definition CROSS JOIN %s.file ON file.id = \
        definition.file WHERE definition.id = ?1"
       schema schema) [ Integer definition ] (fun row ->
      (Sql.read_blob row 0, Sql.read_integer row 1))

let find_text store schema ~definition =
  let schema = name_schema schema in
  Sql.find_row store.sql
    (Printf.sprintf
       "SELECT substr(file.text, definition.base + 1, definition.stop - definition.base) FROM \
        %s.definition CROSS JOIN %s.file ON file.id = definition.file WHERE definition.id = ?1"
       schema schema) [ Integer definition ] (fun row -> Sql.read_blob row 0)

let find_definition_key store schema ~id =
  Sql.find_row store.sql
    (Printf.sprintf "SELECT key FROM %s.definition WHERE id = ?1" (name_schema schema))
    [ Integer id ]
    (fun row -> Sql.read_blob row 0)

let list_member_keys store schema ~owner ~member ~origin =
  Sql.list_rows store.sql
    (Printf.sprintf
       "SELECT key FROM %s.definition WHERE owner = ?1 AND member = ?2 AND origin = ?3 AND ordinal \
        = 0"
       (name_schema schema))
    [ Integer owner; Text member; Integer origin ]
    (fun row -> Sql.read_blob row 0)

type declared = { kind : int; visibility : int; is_generic : bool }

let find_declared store schema ~id : declared option =
  Sql.find_row store.sql
    (Printf.sprintf "SELECT kind, visibility, is_generic FROM %s.definition WHERE id = ?1"
       (name_schema schema))
    [ Integer id ]
    (fun row ->
      {
        kind = Sql.read_integer row 0;
        visibility = Sql.read_integer row 1;
        is_generic = Sql.read_integer row 2 <> 0;
      })

type placement = { file : int option; container : int option }

let find_placement store schema ~id : placement option =
  let read row column =
    if Sql.is_null row column then None else Some (Sql.read_integer row column)
  in
  Sql.find_row store.sql
    (Printf.sprintf "SELECT file, container FROM %s.definition WHERE id = ?1" (name_schema schema))
    [ Integer id ]
    (fun row -> { file = read row 0; container = read row 1 })

let list_containers_of_member store schema ~package ~member ~container_kind =
  let schema = name_schema schema in
  Sql.list_rows store.sql
    (Printf.sprintf
       "SELECT container.key, file.key, method.position FROM %s.definition method CROSS JOIN \
        %s.definition container ON container.id = method.container CROSS JOIN %s.file ON file.id = \
        method.file WHERE method.package = ?1 AND method.member = ?2 AND container.kind = ?3 AND \
        container.ordinal = 0"
       schema schema schema) [ Text package; Text member; Integer container_kind ] (fun row ->
      (Sql.read_blob row 0, Sql.read_blob row 1, Sql.read_integer row 2))

let replace_module store ~id ~package ~name ~key =
  Sql.run store.sql
    "INSERT OR REPLACE INTO main.module (id, package, name, key) VALUES (?1, ?2, ?3, ?4)"
    [ Integer id; Text package; Text name; Blob key ]

let remove_module store ~id =
  Sql.run store.sql "DELETE FROM main.module WHERE id = ?1" [ Integer id ]

let find_module_key store schema ~id =
  Sql.find_row store.sql
    (Printf.sprintf "SELECT key FROM %s.module WHERE id = ?1" (name_schema schema))
    [ Integer id ]
    (fun row -> Sql.read_blob row 0)
