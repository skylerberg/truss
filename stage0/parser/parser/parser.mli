type piece = Split.piece = { first : int; stop : int }

val split : Token.t array -> piece list
val is_use : Token.t array -> piece -> bool
val recovers : Diagnostic.Code.parser -> bool
val use_line : Token.t array -> piece -> Syntax.path option * Diagnostic.t list
val parse : Token.t array -> Syntax.file * Diagnostic.t list

type example = Example_definition | Example_signature

val example_definition : Token.t array -> piece -> example * Diagnostic.t list
val example_statement : Token.t array -> piece -> Diagnostic.t list

module For_testing : sig
  val definition : Token.t array -> piece -> Syntax.top_level * Diagnostic.t list
  val begins_statement : Token.kind -> bool
  val spelled_words : string list
end
