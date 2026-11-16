val evaluate_expression :
  Lookups.t -> visiting:Path.t list -> Resolve.resolved -> Syntax.expression -> Z.t option

val evaluate_constant : Lookups.t -> Path.t -> Z.t option
