val lex : Source.t -> Token.t array * Diagnostic.t list

module For_testing : sig
  val can_end : Token.kind -> bool
  val can_begin : Token.kind -> bool
end
