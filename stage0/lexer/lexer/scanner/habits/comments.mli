val scan : Cursor.t -> inline:bool -> bool
(** A comment, an attribute, or a `;` at the cursor, skipped and reported. Inside an interpolation
    it is rejected. [false] when none starts there. *)
