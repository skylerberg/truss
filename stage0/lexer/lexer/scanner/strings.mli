type scan = Cursor.t -> inline:bool -> nesting:int -> Cursor.item

type builder = {
  buffer : Buffer.t;
  mutable text_start : int;
  mutable pairs : (Token.text * Token.interpolation) list;
}

val scan_string :
  Cursor.t ->
  scan:(Cursor.t -> inline:bool -> nesting:int -> Cursor.item) ->
  tag:(string * Token.span) option ->
  nesting:int ->
  Token.kind * Cursor.ending

val scan_ordinary :
  ?closing:char ->
  Cursor.t ->
  scan:(Cursor.t -> inline:bool -> nesting:int -> Cursor.item) ->
  tag:(string * Token.span) option ->
  nesting:int ->
  Token.kind * Cursor.ending

val scan_one_line_raw :
  Cursor.t ->
  scan:(Cursor.t -> inline:bool -> nesting:int -> Cursor.item) ->
  tag:(string * Token.span) option ->
  form:Token.form ->
  nesting:int ->
  literal_start:int ->
  dollars:int ->
  quotes:int ->
  Token.kind * Cursor.ending

val opens_raw_string : Cursor.t -> int -> bool
