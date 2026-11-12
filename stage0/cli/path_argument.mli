type t = { names : string list; member : string option }

val parse : string -> t
val prefix : t -> string list
