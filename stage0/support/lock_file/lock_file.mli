type t

val acquire : string -> t
val acquire_if_free : string -> t option
val release : t -> unit
val with_lock : string -> (unit -> 'a) -> 'a
val is_held : string -> bool
