val comment_message : string
val line_comment : Cursor.t -> unit
val block_comment : Cursor.t -> unit
val semicolon : Cursor.t -> unit
val reject : ?code:Diagnostic.Code.lexer -> Cursor.t -> length:int -> string -> unit
val character_literal_end : ?after_prefix:bool -> Cursor.t -> int -> int option
val attribute : Cursor.t -> unit
val opens_raw_string : Cursor.t -> int -> bool
