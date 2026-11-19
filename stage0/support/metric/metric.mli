type t = Time | Allocations | Allocated_bytes

val all : t list
val show : t -> string
val find : string -> t option
