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

val character_literal : Cursor.t -> tag:string -> literal_start:int -> stop:int -> Token.kind

type prefix_kind = Format | Raw_text | Bytes

val prefixed_string :
  Cursor.t ->
  scan:(Cursor.t -> inline:bool -> nesting:int -> Cursor.item) ->
  prefix:string ->
  start:int ->
  nesting:int ->
  Token.kind * Cursor.ending

val hash_raw_string : Cursor.t -> start:int -> Token.kind option
val closing_delimiter : Cursor.t -> start:int -> delimiter:int -> int option

val quoted_string :
  Cursor.t ->
  scan:(Cursor.t -> inline:bool -> nesting:int -> Cursor.item) ->
  nesting:int ->
  delimiter:int ->
  Token.kind * Cursor.ending

val curly_quoted_string : Cursor.t -> opening_length:int -> closing:string -> Token.kind option
