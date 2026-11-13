val dependencies : Engine.t -> Path.t list -> Graph_types.edge list
val dependents : Engine.t -> Path.t list -> Graph_types.edge list
val reachable : Engine.t -> Path.t list -> Path.Set.t list
val changes : Engine.t -> Engine.t -> (Path.t * string option * Graph_types.difference) list
val overlaps : base:Engine.t -> Engine.t -> Engine.t -> Graph_types.overlap list
