val expression :
  Lookups.t -> visiting:Path.t list -> Resolve.resolved -> Syntax.expression -> Z.t option

val value_of : Lookups.t -> Path.t -> Z.t option
val is_uint64 : Lookups.t -> Path.t -> bool
