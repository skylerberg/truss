type t = Space | Spelled of string | Opening_quote of string

val find : int -> t option
val token : string -> Token.kind option
