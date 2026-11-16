type entry = Space | Spelled of string | Opening_quote of string

val find : int -> entry option
