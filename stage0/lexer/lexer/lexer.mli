val lex : Source.t -> Token.t array * Diagnostic.t list

module For_testing : sig
  val scan : Source.t -> Token.t array * Diagnostic.t list
  val to_original : Source.span Diagnostic.edit list -> Token.t array -> Token.t array
end
