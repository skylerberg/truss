type piece = { first : int; stop : int }

val stop : Token.t array -> first:int -> int
val pieces : Token.t array -> piece list
