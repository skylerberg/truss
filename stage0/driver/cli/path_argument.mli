type t = { prefix : string list; last : string; member : string option }

val parse : string -> t
