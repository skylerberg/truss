type scanned = Lexed of (Token.kind * Cursor.ending) | Skipped

val scan :
  Cursor.t ->
  scan:(Cursor.t -> inline:bool -> nesting:int -> Cursor.item) ->
  nesting:int ->
  scanned option
(** A string or character of another language at the cursor, reported and lexed as the string its
    fix writes, or [Skipped] when it is rejected. [None] when none starts there. *)

val after_name :
  Cursor.t ->
  scan:(Cursor.t -> inline:bool -> nesting:int -> Cursor.item) ->
  nesting:int ->
  start:int ->
  Token.kind ->
  (Token.kind * Cursor.ending) option
(** The string that a prefix of another language, the name from [start] to the cursor, opens, as [r]
    in `r"..."`. [None] when no string follows. *)

val curly_quoted_string : Cursor.t -> opening_length:int -> closing:string -> Token.kind option
(** Text between curly quotes, as a word processor writes a string. *)
