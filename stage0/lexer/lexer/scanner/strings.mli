val scan_string :
  Cursor.t ->
  scan:(Cursor.t -> inline:bool -> nesting:int -> Cursor.item) ->
  tag:(string * Source.span) option ->
  nesting:int ->
  Token.kind * Cursor.ending

val scan_ordinary :
  ?closing:char ->
  Cursor.t ->
  scan:(Cursor.t -> inline:bool -> nesting:int -> Cursor.item) ->
  tag:(string * Source.span) option ->
  nesting:int ->
  Token.kind * Cursor.ending

val scan_one_line_raw :
  Cursor.t ->
  scan:(Cursor.t -> inline:bool -> nesting:int -> Cursor.item) ->
  tag:(string * Source.span) option ->
  form:Token.form ->
  nesting:int ->
  literal_start:int ->
  dollars:int ->
  quotes:int ->
  Token.kind * Cursor.ending

val opens_raw_string : Cursor.t -> int -> bool
