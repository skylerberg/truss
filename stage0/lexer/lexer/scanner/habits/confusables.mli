type scanned = Lexed of Token.kind | Spaced

val scan : Cursor.t -> value:int -> length:int -> scanned option
(** The confusable character [value], [length] bytes at the cursor: reported, and lexed as its ASCII
    spelling, or skipped when it is a space. [None] when it is not a confusable character. *)
