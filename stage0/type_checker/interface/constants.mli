type outcome =
  | Folded of Z.t
  | Not_folded
  | Fails of Integer_arithmetic.failure * Syntax.expression
  | Depends_on_failure

val evaluate_expression : Lookups.t -> Resolve.resolved -> Types.ty -> Syntax.expression -> outcome
val evaluate_constant : Lookups.t -> Path.t -> outcome
val evaluate_count : Lookups.t -> Path.t -> written:string -> (Z.t, string) result
