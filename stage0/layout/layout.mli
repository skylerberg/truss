(** Inserts [Newline] tokens and matches brackets. See LEXER.md, "Layout". *)

val can_end : Token.kind -> bool
(** Whether a token can end a statement, as GRAMMAR.md lists them. *)

val can_begin : Token.kind -> bool
(** Whether a token can begin a statement, as GRAMMAR.md lists them. *)

type mode =
  | File of { recovery : bool }
      (** A whole file. With [recovery], a definition keyword in column 0
          closes every open bracket. Without it, brackets still open at the
          end of the file make {!run} return [None], so the lexer can run
          again with recovery turned on. *)
  | Interpolation of { cut_off : unit -> bool }
      (** An interpolation's tokens. Brackets still open at its end are
          closed there, and no [Newline] comes before its [End_of_file].
          [cut_off] says, once the end is reached, whether the
          interpolation ended at an error the scanner already reported
          instead of at its closing brace; brackets it left open are then
          closed without another error. *)

val run :
  source:Source.t ->
  diagnostics:Diagnostic.Collector.t ->
  mode:mode ->
  (unit -> Token.raw) ->
  Token.t array option
(** Pulls raw tokens until [End_of_file] and returns the laid-out tokens,
    ending with [End_of_file]. Brackets in the result are always balanced:
    zero-width closers are inserted for openers that are never closed, and
    closers that match nothing are dropped. *)
