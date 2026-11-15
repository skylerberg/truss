val recovers : Diagnostic.Code.parser -> bool
val parse : Token.t array -> Syntax.file * Diagnostic.t list

module For_testing : sig
  type piece = Split.piece = { first : int; stop : int }
  type example = Example_definition | Example_signature

  val split : Token.t array -> piece list
  val is_use : Token.t array -> piece -> bool
  val parse_use_line : Token.t array -> piece -> Syntax.path option Syntax.item * Diagnostic.t list
  val parse_definition : Token.t array -> piece -> Syntax.top_level * Diagnostic.t list
  val parse_example_definition : Token.t array -> piece -> example * Diagnostic.t list
  val parse_example_statement : Token.t array -> piece -> Diagnostic.t list
  val begins_statement : Token.kind -> bool
  val contextual_keywords : string list
end
