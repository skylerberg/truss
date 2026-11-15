type scanned = Lexed of Token.kind | Spaced

val scan : Cursor.t -> value:int -> length:int -> scanned option
