(** The lexer's entry point. See LEXER.md.

    Lexing is a pure function of one file's text. It always returns tokens,
    even for a broken file: brackets are balanced, interpolations are nested
    token arrays, and [Newline] tokens follow GRAMMAR.md's line-break rule.
    The array ends with [End_of_file]. *)

val lex : ?check_fixes:bool -> Source.t -> Token.t array * Diagnostic.t list
(** With [check_fixes], the default, every fix offered has been applied and
    the result lexed again: it removes its diagnostic and adds no other.
    Fixes that fail the check are left out. Tests turn the check off to see
    which fixes would fail it. *)
