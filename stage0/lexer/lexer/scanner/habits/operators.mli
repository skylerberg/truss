type scanned = Lexed of Token.kind | Skipped

val scan : Cursor.t -> follows_operand:bool -> operand_follows:(int -> bool) -> scanned option
(** An operator of another language at the cursor, reported and lexed as the Truss operator it
    stands for, or [Skipped] when it stands for none. [None] when none starts there. *)
