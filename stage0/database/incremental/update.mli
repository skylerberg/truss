val phase_error : Nodes.node -> string -> 'a

val ensure_result :
  Nodes.t -> ('key, 'value) Nodes.query -> ('key, 'value) Nodes.result_cell -> unit

val compute : Nodes.t -> ('key, 'value) Nodes.query -> ('key, 'value) Nodes.result_cell -> unit
val mark_seeds : Nodes.t -> int -> unit
val settle : ?through:int -> Nodes.t -> unit
val check_can_change : Nodes.t -> unit
