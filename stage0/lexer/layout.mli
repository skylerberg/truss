(** Inserts [Newline] tokens and matches brackets.

    Each function calls its last argument for the next raw token until it returns [End], and returns
    the tokens, ending with [End_of_file]. Layout makes each token from its raw token, adding the
    line-break flags. Brackets in the result are always balanced: zero-width closers are inserted
    for openers that are never closed, and closers that match nothing are dropped. An unclosed
    bracket's fix closes it where the indentation says it was meant to close. *)

type input =
  | Next of {
      kind : Token.kind;
      span : Source.span;
      first_line_break : Source.span option;
      blank_line : bool;
      unterminated_string : bool;
    }
      (** The next token, with the first line break before it, if any, whether a blank line came
          before it, and whether it is an unterminated string, an error already reported. *)
  | End of {
      position : int;
      first_line_break : Source.span option;
      blank_line : bool;
      ends_unterminated : bool;
    }
      (** The end of the input. [ends_unterminated] says whether it ends inside an unterminated
          construct, an error the scanner already reported: an interpolation that a line break
          ended, or a file that ends inside a comment or a raw string. Brackets left open are then
          closed without another error. *)

val can_end : Token.kind -> bool
(** Whether a token can end a statement. *)

val can_begin : Token.kind -> bool
(** Whether a token can begin a statement. *)

val file :
  source:Source.t ->
  diagnostics:Diagnostic.Collector.t ->
  recovery:bool ->
  (unit -> input) ->
  Token.t array * bool
(** A whole file, and whether any bracket was still open at its end. With [recovery], a definition
    starting in column 0 closes every open bracket; the lexer turns it on only for a file that left
    a bracket open. *)

val interpolation :
  source:Source.t -> diagnostics:Diagnostic.Collector.t -> (unit -> input) -> Token.t array
(** An interpolation's tokens. Brackets still open at its end are closed there, and no [Newline]
    comes before its [End_of_file]. *)

val starts_definition : Source.t -> int -> bool
(** Whether a definition starts at this offset: a definition keyword in column 0, where `truss fmt`
    puts the start of every definition. Bracket recovery and the note on an unterminated raw string
    use this one rule. *)
