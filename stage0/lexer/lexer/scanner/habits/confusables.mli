type scanned = Lexed of Token.kind | Spaced

val scan : Cursor.t -> scalar_value:Uchar.t -> length:int -> scanned option
