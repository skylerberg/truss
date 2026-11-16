type t = int * int * int

val parse : string -> t option
val show : t -> string
val compare : t -> t -> int
val parse_major : Path.package -> int
val make_first_version : Path.package -> t
