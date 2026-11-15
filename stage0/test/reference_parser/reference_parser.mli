type entry

val file : entry
val accepts : entry -> Token.t list -> bool
val conflicts_resolved_by_precedence : int

module Snippet : sig
  type kind = Use | Definition | Signature | Statement
  type item = { kind : kind; first : int; stop : int }

  val parse : Token.t array -> item list * Diagnostic.t list
  val entry : kind -> entry
end
