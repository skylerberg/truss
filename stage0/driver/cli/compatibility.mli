type change = Breaks of string | Grows of string
type public_change = { path : Path.t; change : change }

val compare :
  before:Interface.Lookups.t -> after:Interface.Lookups.t -> Path.package -> public_change list

val breaks : public_change list -> (Path.t * string) list
val grows : public_change list -> (Path.t * string) list
