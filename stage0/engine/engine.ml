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
