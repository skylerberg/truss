type t

val empty : t
val add : Logic.term -> t -> t
val count : t -> int
val list_oldest_first : t -> Logic.term list
val list_newest_since : t -> count:int -> Logic.term list
val remove_held : t -> under:Logic.term -> Logic.term -> Logic.term
