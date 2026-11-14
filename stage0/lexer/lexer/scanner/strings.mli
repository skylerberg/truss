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
  ?closing:int ->
  Cursor.t ->
  scan:(Cursor.t -> inline:bool -> nesting:int -> Cursor.item) ->
  tag:(string * Token.span) option ->
  nesting:int ->
  Token.kind * Cursor.ending
(** An ordinary string at its opening quote, closed by [closing], a quote unless given. *)

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
(** A raw string's text on its line, after its opening delimiter. *)

val opens_raw_string : Cursor.t -> int -> bool
(** Whether a run of `$` at [index] opens a raw string. *)
