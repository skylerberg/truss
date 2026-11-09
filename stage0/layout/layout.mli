(** Inserts [Newline] tokens and matches brackets. See LEXER.md, "Layout".

    Each function pulls raw tokens until [End_of_file] and returns the
    tokens, ending with [End_of_file]. Layout makes each token from its raw
    token, adding the line-break flags. Brackets in the result are always
    balanced: zero-width closers are inserted for openers that are never
    closed, and closers that match nothing are dropped. *)

val can_end : Token.kind -> bool
(** Whether a token can end a statement, as GRAMMAR.md lists them. *)

val can_begin : Token.kind -> bool
(** Whether a token can begin a statement, as GRAMMAR.md lists them. *)

val file :
  source:Source.t ->
  diagnostics:Diagnostic.Collector.t ->
  cut_off:(unit -> bool) ->
  (unit -> Token.raw) ->
  [ `Complete of Token.t array | `Unclosed_at_end ]
(** A whole file. If brackets are still open at its end, it stops, so that
    the lexer can run again with {!file_with_recovery}. [cut_off] says, at
    the end, whether the file ended inside an unterminated comment or
    string, which the scanner has reported; brackets left open are then
    closed without another error. *)

val file_with_recovery :
  source:Source.t ->
  diagnostics:Diagnostic.Collector.t ->
  cut_off:(unit -> bool) ->
  (unit -> Token.raw) ->
  Token.t array
(** A whole file, where a definition starting in column 0 closes every open
    bracket. *)

val interpolation :
  source:Source.t ->
  diagnostics:Diagnostic.Collector.t ->
  cut_off:(unit -> bool) ->
  (unit -> Token.raw) ->
  Token.t array
(** An interpolation's tokens. Brackets still open at its end are closed
    there, and no [Newline] comes before its [End_of_file]. [cut_off] says,
    once the end is reached, whether the interpolation ended at an error the
    scanner already reported instead of at its closing brace; brackets it
    left open are then closed without another error. *)
