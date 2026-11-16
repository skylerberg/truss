type scanned = Lexed of (Token.kind * Cursor.ending) | Skipped

val scan :
  Cursor.t ->
  scan:(Cursor.t -> inline:bool -> nesting:int -> Cursor.item) ->
  nesting:int ->
  scanned option

val lex_after_name :
  Cursor.t ->
  scan:(Cursor.t -> inline:bool -> nesting:int -> Cursor.item) ->
  nesting:int ->
  start:int ->
  Token.kind ->
  (Token.kind * Cursor.ending) option

val lex_curly_quoted_string : Cursor.t -> opening_length:int -> closing:string -> Token.kind option
