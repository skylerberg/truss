open Tree

val nested_blocks : statement -> block list
val iter_places_read : (place -> unit) -> block -> unit
val constants_named : Graph.t -> Path.t list
val iter_code : (statement -> unit) -> t -> unit
val iter_formula : (statement -> unit) -> formula -> unit
val operand_type : operand -> Types.ty
