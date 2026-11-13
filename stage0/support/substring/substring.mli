(** Finding one text in another. *)

val find : ?occurrence:int -> string -> string -> int option
(** [find text part] is the offset of the first occurrence of [part] in [text], and with
    [~occurrence], of that occurrence, counting from 1; [None] if there are fewer. *)

val contains : string -> string -> bool
(** Whether [part] occurs in [text]. *)
