(* The database's view of the engine. See engine.mli. *)

type t = Incremental.t

let create = Incremental.create
let frozen_layer = Incremental.frozen_layer
let context = Incremental.context
let of_context = Incremental.engine_of
let set = Incremental.set
let remove = Incremental.remove
let get engine query key = Incremental.demand (Incremental.context engine) query key
let release = Incremental.release
let fork = Incremental.fork

type node = Incremental.node
type change = Incremental.change = { computed : node list; changed : node list }

let stabilize = Incremental.stabilize
let executed = Incremental.executed
let clear_log = Incremental.clear_log
let nodes = Incremental.nodes
let label = Incremental.label
let subject = Incremental.subject
let reads = Incremental.reads
let readers = Incremental.readers
let counterpart = Incremental.counterpart
let same_outcome = Incremental.same_outcome

(* Saving and loading *)

type record =
  | Base of Incremental.saved_node list
  | Changes of { nodes : Incremental.saved_node list; dropped : int list }

let attach engine store = Incremental.set_store engine ~put:(Store.put store) ~get:(Store.get store)

(* The size of each journal's last base, so that the changes after it are
   folded into a new base once they outgrow it. *)
let base_sizes : (string, int) Hashtbl.t = Hashtbl.create 8
let journal_key = Store.journal_name

let save_all engine journal =
  let bytes = Marshal.to_string (Base (Incremental.everything_to_save engine)) [] in
  Store.compact journal bytes;
  Hashtbl.replace base_sizes (journal_key journal) (String.length bytes)

let save engine journal =
  let base = Hashtbl.find_opt base_sizes (journal_key journal) in
  match base with
  | None -> save_all engine journal
  | Some base ->
      let nodes, dropped = Incremental.changes_to_save engine in
      if nodes <> [] || dropped <> [] then begin
        Store.append journal (Marshal.to_string (Changes { nodes; dropped }) []);
        if Store.journal_size journal > max (2 * base) (1024 * 1024) then save_all engine journal
      end

let replay journal =
  let state : (int, Incremental.saved_node) Hashtbl.t = Hashtbl.create 1024 in
  let records = Store.records journal in
  List.iter
    (fun bytes ->
      match (Marshal.from_string bytes 0 : record) with
      | Base nodes ->
          Hashtbl.reset state;
          List.iter
            (fun (node : Incremental.saved_node) -> Hashtbl.replace state node.id node)
            nodes
      | Changes { nodes; dropped } ->
          List.iter (Hashtbl.remove state) dropped;
          List.iter
            (fun (node : Incremental.saved_node) -> Hashtbl.replace state node.id node)
            nodes)
    records;
  ( List.sort
      (fun (a : Incremental.saved_node) b -> compare a.id b.id)
      (Hashtbl.fold (fun _ node acc -> node :: acc) state []),
    records )

let load ?log ?shared ?(frozen = false) store journal =
  match replay journal with
  | [], _ -> None
  | nodes, records ->
      let engine = if frozen then frozen_layer ?log () else create ?log ?shared () in
      attach engine store;
      Incremental.restore engine nodes;
      (* The base this process last wrote is not known, so the first save
         after loading compares with the whole journal. *)
      Hashtbl.replace base_sizes (journal_key journal)
        (List.fold_left (fun total r -> total + String.length r) 0 records);
      Some engine

let values_in journal =
  List.filter_map (fun (node : Incremental.saved_node) -> node.value) (fst (replay journal))
