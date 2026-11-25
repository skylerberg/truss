val lex : Source.t -> Token.t array * Syntax_catalog.Lexing.t list

module For_testing : sig
  val scan : Source.t -> Token.t array * Syntax_catalog.Lexing.t list
  val to_original : Source.span Diagnostic.edit list -> Token.t array -> Token.t array
end
