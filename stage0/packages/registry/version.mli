type t = int * int * int

val parse : string -> t option
val show : t -> string
val compare : t -> t -> int
val major_of_name : Path.package -> int
val first : Path.package -> t
