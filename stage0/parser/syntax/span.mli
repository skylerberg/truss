type t = private { start : int; stop : int }

val make : int -> int -> t
val zero_width : int -> t
val to_source : base:int -> t -> Source.span
val of_source : base:int -> Source.span -> t
