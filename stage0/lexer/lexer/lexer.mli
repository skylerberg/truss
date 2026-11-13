(** The lexer's entry point.

    Lexing is a pure function of one file's text. It always returns tokens, even for a broken file:
    brackets are balanced, interpolations are nested token arrays, and [Newline] tokens follow the
    grammar's line-break rule. The array ends with [End_of_file]. *)

val lex : Source.t -> Token.t array * Diagnostic.t list

(** The lexer's own modules, for its tests. *)
module For_testing : sig
  val can_end : Token.kind -> bool
  (** Whether a token can end a statement. *)

  val can_begin : Token.kind -> bool
  (** Whether a token can begin a statement. *)
end
