val scan_end : string -> int -> int
(** The end of the number that starts at the offset, with the forms of other languages. *)

val check : string -> Numbers.checked
(** A literal, checked for the forms of other languages and then against Truss's grammar. *)

val after_integer :
  Cursor.t -> start:int -> stop:int -> word_follows:(int -> bool) -> Numbers.checked -> Token.kind
(** The token of the checked number from [start] to [stop]: a float when a `.` with no digit follows
    an integer, as in `1.`, and otherwise its value. *)

val leading_dot : Cursor.t -> Token.kind option
(** `.5` at the cursor, where no operand comes before the `.`, as the float `0.5`. [None] when it is
    not a float. *)
