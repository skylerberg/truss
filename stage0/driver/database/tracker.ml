type t = {
  store : Store.t;
  records_reads : bool;
  bugs : (int * int, Compiler_bug.t) Hashtbl.t;
  broken : (int * int, unit) Hashtbl.t;
}

let create store ~records_reads =
  { store; records_reads; bugs = Hashtbl.create 8; broken = Hashtbl.create 8 }

let failing_unit : (Kind.stage * int * exn option) option ref = ref None

let with_failing_unit ?raising stage id run =
  failing_unit := Some (stage, id, raising);
  Fun.protect ~finally:(fun () -> failing_unit := None) run

let fail_for_test stage ids =
  match !failing_unit with
  | Some (failing_stage, id, raising) when failing_stage = stage && List.mem id ids -> (
      match raising with
      | Some raised -> raise raised
      | None -> Compiler_bug.raise_bug ~stage:"Database" "a unit fails for a test")
  | Some _ | None -> ()

let reset_broken tracker = Hashtbl.reset tracker.broken
let is_broken tracker stage id = Hashtbl.mem tracker.broken (Kind.rank_stage stage, id)

let record_bug tracker stage ids bug =
  List.iter
    (fun id ->
      Hashtbl.replace tracker.bugs (Kind.rank_stage stage, id) bug;
      Hashtbl.replace tracker.broken (Kind.rank_stage stage, id) ())
    ids

type recorder = { note : Kind.marker -> Kind.target -> int -> string -> unit }

let untracked = { note = (fun _ _ _ _ -> ()) }
let reads = Kind.encode_markers [ Reads ]

let locate (target : Kind.target) id name : Store.endpoint =
  { kind = Kind.rank_target target; id; name }

let locate_unit stage id : Store.endpoint = { kind = Kind.rank_stage stage; id; name = "" }
let mark_stale tracker stage id = Store.mark_stale tracker.store ~stage:(Kind.rank_stage stage) ~id

let mark_readers tracker target id name =
  if tracker.records_reads then
    Store.mark_sources_stale tracker.store ~target:(locate target id name) ~markers:reads

let mark_readers_of_all tracker targets =
  if tracker.records_reads then
    Store.mark_readers_of_targets tracker.store
      ~targets:(List.map (fun (target, id, name) -> locate target id name) targets)
      ~markers:reads

let stages_holding_positions =
  List.fold_left (fun stages stage -> stages lor (1 lsl Kind.rank_stage stage)) 0 [ Kind.Lower ]

let mark_position_holders tracker target id name =
  if tracker.records_reads then
    Store.mark_position_holders_stale tracker.store ~target:(locate target id name) ~markers:reads
      ~stages:stages_holding_positions

let import_kind = Kind.rank_target (Entity Import)
let definition_kind = Kind.rank_target (Entity Definition)

let proof_graph : Store.proof_graph =
  {
    unit_kind = Kind.rank_stage List_calls;
    node_kind = definition_kind;
    markers = Kind.encode_markers [ Calls; Assumes ];
  }

let package_kind = Kind.rank_target (Entity Package)

let follow_edge_changes tracker (stage : Kind.stage) id changes =
  let differs (change : Store.edge_change) marker =
    Kind.has_marker change.before marker <> Kind.has_marker change.after marker
  in
  if stage = Check_body && tracker.records_reads then begin
    (match
       List.filter_map
         (fun (change : Store.edge_change) ->
           if change.changed.kind = definition_kind && differs change References then
             Some change.changed.id
           else None)
         changes
     with
    | [] -> ()
    | used ->
        Store.mark_paths_stale tracker.store ~stage:(Kind.rank_stage Check_unexported) ~paths:used);
    if
      List.exists
        (fun (change : Store.edge_change) ->
          change.changed.kind = definition_kind
          && (differs change Instantiates || differs change Grows))
        changes
    then begin
      mark_stale tracker Check_instantiation id;
      Store.mark_reported_units_stale tracker.store ~stage:(Kind.rank_stage Check_instantiation)
    end;
    List.iter
      (fun (change : Store.edge_change) ->
        if change.changed.kind = package_kind && differs change References then
          mark_readers tracker (Selection Package_references) change.changed.id change.changed.name)
      changes
  end;
  List.iter
    (fun (change : Store.edge_change) ->
      if change.changed.kind = import_kind && differs change References then
        mark_readers tracker (Selection Import_references) change.changed.id "")
    changes;
  if stage = List_calls then
    begin if
      List.exists
        (fun (change : Store.edge_change) ->
          change.changed.kind = definition_kind && (differs change Calls || differs change Assumes))
        changes
    then begin
      mark_stale tracker Group_recursion id;
      Store.mark_groups_stale tracker.store ~stage:(Kind.rank_stage Group_recursion) ~path:id
    end
    end

let replace_edges tracker stage id edges =
  let changes = Store.replace_edges tracker.store ~source:(locate_unit stage id) edges in
  follow_edge_changes tracker stage id changes;
  changes

type observation =
  | Computed of { stage : Kind.stage; ids : int list; reads : int; distinct_reads : int }
  | Unchanged of { stage : Kind.stage; id : int }
  | Written of { stage : Kind.stage; id : int; is_removal : bool }

let observer : (observation -> unit) ref = ref ignore

let with_observer observe run =
  let previous = !observer in
  observer := observe;
  Fun.protect ~finally:(fun () -> observer := previous) run

let count_reads noted =
  Hashtbl.fold
    (fun _ markers count -> if Kind.has_marker markers Reads then count + 1 else count)
    noted 0

let list_noted_edges tracker noted =
  Hashtbl.fold
    (fun target markers edges ->
      match if tracker.records_reads then markers else markers land lnot reads with
      | 0 -> edges
      | markers -> { Store.target; markers } :: edges)
    noted []

let record_observed tracker stage id compute =
  let noted = Hashtbl.create 16 in
  let read_count = ref 0 in
  let note (marker : Kind.marker) target target_id name =
    if marker = Reads then incr read_count;
    let endpoint = locate target target_id name in
    Hashtbl.replace noted endpoint
      (Option.value (Hashtbl.find_opt noted endpoint) ~default:0 lor Kind.encode_markers [ marker ])
  in
  let result = compute { note } in
  !observer
    (Computed { stage; ids = [ id ]; reads = !read_count; distinct_reads = count_reads noted });
  (result, replace_edges tracker stage id (list_noted_edges tracker noted))

let record tracker stage id compute = fst (record_observed tracker stage id compute)

let record_group tracker stage ids ~own compute =
  let noted = Hashtbl.create 16 in
  let read_count = ref 0 in
  let own_kinds = List.map (fun fact -> Kind.rank_target (Fact fact)) own in
  let note (marker : Kind.marker) target target_id name =
    if marker = Reads then incr read_count;
    let endpoint = locate target target_id name in
    if not (List.mem endpoint.kind own_kinds && List.mem target_id ids) then
      Hashtbl.replace noted endpoint
        (Option.value (Hashtbl.find_opt noted endpoint) ~default:0
        lor Kind.encode_markers [ marker ])
  in
  let result = compute { note } in
  !observer (Computed { stage; ids; reads = !read_count; distinct_reads = count_reads noted });
  let edges = list_noted_edges tracker noted in
  List.iter (fun id -> ignore (replace_edges tracker stage id edges)) ids;
  result

let remove_edges tracker stage id = ignore (replace_edges tracker stage id [])

type 'value outcome = Value of 'value | Failed | Blocked
type state = Has_value | Has_failed | Is_blocked

exception Reads_failed_fact

type 'value view = {
  table : string;
  stage : Kind.stage;
  targets : Kind.fact list;
  stored : Store.fact;
  width : int;
  id_column : string;
  is_keyed_by_path : bool;
  decode : Store.cell array -> 'value;
  guard : guard option;
}

and guard = { guard_stage : Kind.stage; guard_table : string }

type 'value fact = {
  whole : 'value view;
  groups : (Kind.fact * int) list;
  encode : 'value -> Store.cell list;
}

type any_fact = Any : 'value fact -> any_fact

let make_stored ~table ~id_column ~fixed ~columns =
  Store.make_fact ~table ~id_column ~fixed ~columns:("state" :: columns)

let facts_of_stages : (Kind.stage, any_fact) Hashtbl.t = Hashtbl.create 32
let list_facts stage = List.rev (Hashtbl.find_all facts_of_stages stage)

let make_fact ~stage ~table ~id_column ~fixed ~groups ~encode ~decode =
  let columns = List.concat_map snd groups in
  let fact =
    {
      whole =
        {
          table;
          stage;
          targets = List.map fst groups;
          stored = make_stored ~table ~id_column ~fixed ~columns;
          width = List.length columns;
          id_column;
          is_keyed_by_path = id_column = "path";
          decode;
          guard = None;
        };
      groups = List.map (fun (target, columns) -> (target, List.length columns)) groups;
      encode;
    }
  in
  Hashtbl.add facts_of_stages stage (Any fact);
  fact

let make_view ~stage ~table ~id_column ~fixed ~target ~columns ~decode =
  {
    table;
    stage;
    targets = [ target ];
    stored = make_stored ~table ~id_column ~fixed ~columns;
    width = List.length columns;
    id_column;
    is_keyed_by_path = id_column = "path";
    decode;
    guard = None;
  }

let guard_view view ~stage ~table ~id_column ~targets =
  {
    view with
    targets;
    stored = Store.guard_fact view.stored ~table ~id_column;
    guard = Some { guard_stage = stage; guard_table = table };
  }

let marshal value = Store.Blob (Marshal.to_string value [])

let unmarshal : Store.cell -> 'value = function
  | Blob bytes -> Marshal.from_string bytes 0
  | Text _ | Integer _ | Null ->
      Compiler_bug.raise_bug ~stage:"Database" "a column that holds a marshaled value holds none"

let decode_state table : Store.cell -> state = function
  | Integer 0 -> Has_value
  | Integer 1 -> Has_failed
  | Integer 2 -> Is_blocked
  | Blob _ | Text _ | Integer _ | Null ->
      Compiler_bug.raise_bug ~stage:"Database" "a row of %s holds no state" table

let decode view (cells : Store.cell array) =
  match decode_state view.table cells.(0) with
  | Has_value -> Value (view.decode (Array.sub cells 1 view.width))
  | Has_failed -> Failed
  | Is_blocked -> Blocked

let encode fact : _ outcome -> Store.cell list = function
  | Value value -> Integer 0 :: fact.encode value
  | Failed -> Integer 1 :: List.init fact.whole.width (fun _ -> Store.Null)
  | Blocked -> Integer 2 :: List.init fact.whole.width (fun _ -> Store.Null)

let find_row tracker recorder view package ~id =
  List.iter (fun target -> recorder.note Reads (Fact target) id "") view.targets;
  let stages =
    view.stage :: List.map (fun guard -> guard.guard_stage) (Option.to_list view.guard)
  in
  let find_in schema =
    Store.find_fact tracker.store schema view.stored ~id ~stages:(List.map Kind.rank_stage stages)
  in
  let schema = Store.locate_schema tracker.store package in
  match find_in schema with
  | Absent when view.is_keyed_by_path && schema <> Main -> find_in Main
  | row -> row

let decode_row view (cells : Store.cell array) =
  List.iter
    (fun guard ->
      match cells.(Array.length cells - 1) with
      | Integer 0 -> ()
      | Integer _ -> raise Reads_failed_fact
      | Null ->
          Compiler_bug.raise_bug ~stage:"Database" "a row of %s is not computed" guard.guard_table
      | Blob _ | Text _ ->
          Compiler_bug.raise_bug ~stage:"Database" "a row of %s holds no state" guard.guard_table)
    (Option.to_list view.guard);
  decode view cells

let find tracker recorder view package ~id =
  match find_row tracker recorder view package ~id with
  | Current cells -> Some (decode_row view cells)
  | Absent -> None
  | Stale -> (
      match
        List.find_map
          (fun stage -> Hashtbl.find_opt tracker.bugs (Kind.rank_stage stage, id))
          (view.stage :: List.map (fun guard -> guard.guard_stage) (Option.to_list view.guard))
      with
      | Some bug -> raise (Compiler_bug.Bug bug)
      | None ->
          Compiler_bug.raise_bug ~stage:"Database" "a row of %s is read while its unit is stale"
            view.table)

let find_settled tracker recorder view package ~id =
  match find_row tracker recorder view package ~id with
  | Current cells -> Some (decode_row view cells)
  | Absent | Stale -> None

let read tracker recorder view package ~id =
  match find tracker recorder view package ~id with
  | Some outcome -> outcome
  | None -> Compiler_bug.raise_bug ~stage:"Database" "a row of %s is not computed" view.table

let require_value = function Value value -> value | Failed | Blocked -> raise Reads_failed_fact

let read_value tracker recorder view package ~id =
  require_value (read tracker recorder view package ~id)

let find_value tracker recorder view package ~id =
  Option.map require_value (find tracker recorder view package ~id)

let rec list_changed_groups groups before after =
  match groups with
  | [] -> []
  | (target, width) :: rest ->
      let is_equal = List.take width before = List.take width after in
      let changed = list_changed_groups rest (List.drop width before) (List.drop width after) in
      if is_equal then changed else target :: changed

let write_observed tracker fact ~id outcome =
  let stored = fact.whole.stored in
  let before = Store.find_stored_fact tracker.store stored ~id in
  let changed =
    match (before, Option.map (encode fact) outcome) with
    | None, None -> []
    | Some _, None ->
        Store.remove_fact tracker.store stored ~id;
        fact.whole.targets
    | before, Some cells ->
        let changed =
          match Option.map Array.to_list before with
          | Some (state_before :: before) when state_before = List.hd cells ->
              list_changed_groups fact.groups before (List.tl cells)
          | Some _ | None -> fact.whole.targets
        in
        if Option.map Array.to_list before <> Some cells then
          Store.replace_fact tracker.store stored ~id cells;
        changed
  in
  List.iter
    (fun target -> mark_readers tracker (Fact target) id "")
    (List.concat_map Kind.list_read_targets changed);
  !observer
    (if changed = [] then Unchanged { stage = fact.whole.stage; id }
     else Written { stage = fact.whole.stage; id; is_removal = Option.is_none outcome });
  ( Option.map (fun (cells : Store.cell array) -> decode_state fact.whole.table cells.(0)) before,
    changed <> [] )

let write tracker fact ~id outcome = fst (write_observed tracker fact ~id outcome)

let report stage id ~is_changed =
  !observer
    (if is_changed then Written { stage; id; is_removal = false } else Unchanged { stage; id })

let report_computed stage ids = !observer (Computed { stage; ids; reads = 0; distinct_reads = 0 })

let forget tracker stage id =
  List.iter (fun (Any fact) -> ignore (write tracker fact ~id None)) (list_facts stage);
  remove_edges tracker stage id;
  ignore
    (Store.replace_diagnostics tracker.store ~stage:(Kind.rank_stage stage) ~unit:id ~package:"" []);
  ignore (Store.unmark_stale tracker.store ~stage:(Kind.rank_stage stage) ~id)

let encode_diagnostic ~definition ~file (description : _ Description.t) detail : Store.diagnostic =
  {
    definition;
    file;
    is_error = description.severity = Error;
    code = Diagnostic.Code.name description.code;
    detail = Marshal.to_string detail [];
  }

let replace_file_diagnostics tracker stage ~package ~file diagnostics =
  Store.replace_diagnostics tracker.store ~stage:(Kind.rank_stage stage) ~unit:file
    ~package:(Path.show_package package)
    (List.map
       (fun diagnostic ->
         encode_diagnostic ~definition:None ~file:(Some file)
           (Renderer.describe_file_diagnostic diagnostic)
           diagnostic)
       diagnostics)

let replace_placed_diagnostics tracker stage ~package ~unit placed =
  Store.replace_diagnostics tracker.store ~stage:(Kind.rank_stage stage) ~unit
    ~package:(Path.show_package package)
    (List.map
       (fun (definition, diagnostic) ->
         encode_diagnostic ~definition:(Some definition) ~file:None (Catalog.describe diagnostic)
           diagnostic)
       placed)

let replace_definition_diagnostics tracker stage ~package ~definition diagnostics =
  ignore
    (replace_placed_diagnostics tracker stage ~package ~unit:definition
       (List.map (fun diagnostic -> (definition, diagnostic)) diagnostics))

type description = {
  table : string;
  id_column : string;
  targets : Kind.fact list;
  read_targets : Kind.fact list;
}

let describe (Any fact) : description =
  {
    table = fact.whole.table;
    id_column = fact.whole.id_column;
    targets = fact.whole.targets;
    read_targets = List.concat_map Kind.list_read_targets fact.whole.targets;
  }
