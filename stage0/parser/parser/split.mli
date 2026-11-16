type piece = { first : int; stop : int }

val stop : Token.t array -> first:int -> int
val split_pieces : Token.t array -> piece list
