type scanned = Lexed of Token.kind | Ellipsis

val scan : Cursor.t -> scanned option

val lex_ellipsis :
  Cursor.t -> start:int -> follows_operand:bool -> operand_follows:bool -> Token.kind option
