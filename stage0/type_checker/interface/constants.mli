val expression :
  Query.context -> visiting:Path.t list -> Resolve.resolved -> Syntax.expression -> Z.t option
(** Evaluates a constant through the constants that it refers to. [visiting] holds the constants on
    the current path, so that a cycle is detected here and gives no value, instead of becoming a
    query cycle. *)

val value_of : (Path.t, Z.t option) Query.query
val is_uint64 : Query.context -> Path.t -> bool
