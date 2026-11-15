val expression :
  Query.context -> visiting:Path.t list -> Resolve.resolved -> Syntax.expression -> Z.t option

val value_of : (Path.t, Z.t option) Query.query
val is_usize : Query.context -> Path.t -> bool
