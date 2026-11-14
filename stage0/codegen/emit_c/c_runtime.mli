type build = Development | Release
type linkage = External | Internal
type site = { definition : Path.t; line : int; column : int }
type failure = Echo | Todo

val bug : ('a, unit, string, 'b) format4 -> 'a
val anchor_symbol : Path.t -> string
val anchor_struct : string
val integer_c : Memory_layout.integer -> string
val unsigned_c : Memory_layout.integer -> string
val signed : Memory_layout.integer -> bool
val integer_typedefs : Memory_layout.target -> string

val declarations_text : build -> string list -> string
(** The runtime's declarations and the helpers that the names in the list stand for, with those they
    need, in an order C accepts. *)
