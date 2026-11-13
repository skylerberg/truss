type change = { computed : Nodes.node list; changed : Nodes.node list }

val stabilize : Nodes.t -> change
val freeze : ?fixed:bool -> Nodes.t -> unit
val unroot : Nodes.t -> ('key, 'value) Nodes.query -> 'key -> unit
val executed : Nodes.t -> string list
val computed : Nodes.t -> ('key, 'value) Nodes.query -> 'key list
val result_label : ('key, 'value) Nodes.query -> 'key -> string
val clear_log : Nodes.t -> unit
val by_id : Nodes.node list -> Nodes.node list
val differing : Nodes.t -> Nodes.node list
val count : Nodes.t -> int
val unshared : Nodes.t -> Nodes.t -> Nodes.node list
val nodes : Nodes.t -> Nodes.node list
val nodes_including_fixed : Nodes.t -> Nodes.node list
val reads : Nodes.t -> Nodes.node -> Nodes.node list
val readers : Nodes.t -> Nodes.node -> Nodes.node list
val current_in : Nodes.node -> Nodes.t -> Nodes.node option
val same_outcome : Nodes.t -> Nodes.node -> Nodes.t -> Nodes.node -> bool
val inputs_stored : Nodes.t -> bool
