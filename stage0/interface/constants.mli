(** The values of integer constants, evaluated exactly where the checker needs them: a [USize] in a
    type argument, as in [Array[UInt8, size]]. Code generation evaluates every other constant.
    Constants that refer to each other in a cycle have no value. *)

val expression :
  Query.context -> visiting:Path.t list -> Resolve.resolved -> Syntax.expression -> Z.t option
(** Evaluates a constant through the constants that it refers to. [visiting] holds the constants on
    the current path, so that a cycle is detected here and gives no value, instead of becoming a
    query cycle. *)

val value_of : (Path.t, Z.t option) Query.query

val is_usize : Query.context -> Path.t -> bool
(** Whether a constant is declared a [USize], as a type argument needs. *)
