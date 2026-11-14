val scan : Cursor.t -> Buffer.t -> bool
(** An escape of another language at the `\` at the cursor, reported and added to [buffer] as the
    character it stands for. [false] when it is none. *)
