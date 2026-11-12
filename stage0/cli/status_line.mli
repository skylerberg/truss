type t = { enabled : bool; mutable drawn : bool }

val create : enabled:bool -> t
val cut : string -> int -> string
val show : t -> string -> unit
val clear : t -> unit
