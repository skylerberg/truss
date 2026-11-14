type context = Code | Ordinary_string | Raw_string

val remove_trivia :
  Cursor.t -> start:int -> stop:int -> line_break:bool -> Diagnostic.span Diagnostic.edit

val forbidden_run : Cursor.t -> context:context -> unit
val invalid_run : Cursor.t -> unit
val copy_plain : Cursor.t -> Buffer.t -> special:(int -> bool) -> unit
val read_character : Cursor.t -> Buffer.t -> context:context -> unit
val consume_line_break : Cursor.t -> Source.span
val note_line_break : Cursor.t -> Source.span -> unit
