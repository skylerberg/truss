val resolve : Nodes.t -> Nodes.node -> Nodes.node
val defer_collection : Nodes.t -> Nodes.node -> unit
val forget : Nodes.t -> Nodes.node -> unit
val collect_or_defer : Nodes.t -> Nodes.node -> unit
val sweep : Nodes.t -> unit
val commit_reads : Nodes.t -> Nodes.node -> Nodes.node list -> unit
val shadow : Nodes.t -> Nodes.node -> Nodes.node
val readers_here : Nodes.t -> Nodes.node -> phase:int option -> Nodes.node list
val mark : ?every_phase:bool -> Nodes.t -> Nodes.node -> unit
val seed : Nodes.t -> Nodes.node -> unit
val record_read : Nodes.context -> Nodes.node -> unit
val cycle : Nodes.t -> Nodes.node -> string list
