type change = Breaks of string | Grows of string
type public_change = { path : Path.t; change : change }

val compare : before:Database.t -> after:Database.t -> Path.package -> public_change list
val list_breaking_changes : public_change list -> (Path.t * string) list
val list_growing_changes : public_change list -> (Path.t * string) list
