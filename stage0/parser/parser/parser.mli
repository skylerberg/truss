type piece = Split.piece = { first : int; stop : int }

val split : Token.t array -> piece list
val is_use : Token.t array -> piece -> bool

type 'value parsed = { value : 'value Syntax.item; diagnostics : Diagnostic.in_definition list }

val diagnostics_in_file : _ parsed -> Diagnostic.t list
val use_line : Source.t -> Token.t array -> piece -> Syntax.path option parsed
val parse : Source.t -> Token.t array -> Syntax.file * Diagnostic.t list

type example = Example_definition | Example_signature

val example_definition : Source.t -> Token.t array -> piece -> example * Diagnostic.t list
val example_statement : Source.t -> Token.t array -> piece -> Diagnostic.t list

module For_testing : sig
  val definition :
    Source.t -> Token.t array -> piece -> Syntax.definition parsed * Syntax.definition parsed list

  val begins_statement : Token.kind -> bool
  val spelled_words : string list
end
