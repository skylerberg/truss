val parse :
  Token.t array ->
  lexer_diagnostics:Syntax_catalog.Lexing.t list ->
  Syntax.file * Syntax_catalog.Parsing.t list

val parse_source : Source.t -> Syntax.file * Syntax_catalog.Syntax_diagnostic.t list

module For_testing : sig
  type piece = Split.piece = { first : int; stop : int }
  type example = Example_definition | Example_signature

  val split : Token.t array -> piece list
  val is_use : Token.t array -> piece -> bool

  val parse_use_line :
    Token.t array -> piece -> Syntax.path option Syntax.item * Syntax_catalog.Parsing.t list

  val parse_definition : Token.t array -> piece -> Syntax.top_level * Syntax_catalog.Parsing.t list
  val parse_example_definition : Token.t array -> piece -> example * Syntax_catalog.Parsing.t list
  val parse_example_statement : Token.t array -> piece -> Syntax_catalog.Parsing.t list
  val begins_statement : Token.kind -> bool
  val contextual_keywords : string list
end
