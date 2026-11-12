type t = Incremental.t

let seal = Incremental.seal
let create = Incremental.create
let freeze = Incremental.freeze
let context = Incremental.context
let observer = Incremental.observer
let of_context = Incremental.engine_of
let set = Incremental.set
let remove = Incremental.remove
let get engine query key = Incremental.demand (Incremental.context engine) query key
let unroot = Incremental.unroot

type node = Incremental.node
type change = Incremental.change = { computed : node list; changed : node list }

let stabilize = Incremental.stabilize
let executed = Incremental.executed
let clear_log = Incremental.clear_log

type counters = Incremental.counters = {
  marked : int;
  confirmed : int;
  computed : int;
  changed : int;
  adopted : int;
  copied : int;
  collected : int;
}

let counters = Incremental.counters
let nodes = Incremental.nodes
let differing = Incremental.differing
let unshared = Incremental.unshared
let identity = Incremental.identity
let count = Incremental.count
let label = Incremental.label
let subject = Incremental.subject
let is_input = Incremental.is_input
let is_fixed = Incremental.is_fixed
let reads = Incremental.reads
let readers = Incremental.readers
let current_in = Incremental.current_in
let same_outcome = Incremental.same_outcome

(* States and facts in the store *)

let store_of store ~version : Incremental.store =
  {
    id = Store.directory store;
    version;
    put = Store.put store;
    get = Store.get store;
    find = (fun ~kind ~key -> Store.find_result store ~kind ~key);
    add = (fun ~kind ~key value -> Store.add_result store ~kind ~key value);
  }

let attach engine store ~version = Incremental.attach engine (store_of store ~version)
let record = Incremental.record
let write = Incremental.write

type debt = Incremental.debt = { whole : int; differences : int; depth : int }

let debt = Incremental.debt
let unwritten = Incremental.unwritten
let artifact = Incremental.artifact

let open_base store ~version ~bases name =
  Incremental.frozen_of (store_of store ~version) ~bases ~fixed:true name

let open_ ?log store ~version ~bases name =
  Incremental.open_ ?log (store_of store ~version) ~bases name

exception Lost = Incremental.Lost

let inputs_stored = Incremental.inputs_stored
let values_in store ~version name = Incremental.values_in (store_of store ~version) name
let forget_bases = Incremental.forget_bases

let audit ?flat ?before engine =
  Incremental.audit ?flat ?before:(Option.map Query.phase_rank before) engine

let audit_all = Incremental.audit_all
let auditing = Incremental.auditing
let skip_audit = Incremental.skip_audit
