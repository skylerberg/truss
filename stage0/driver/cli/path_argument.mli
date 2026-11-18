type t = { prefix : string list; last : string; member : string option }

val parse : string -> t

type target = Package of Path.package | Module of Path.module_ | Definition of Path.t

val resolve : Resolve.Names.lookups -> Path.package list -> t -> target list
val is_shown : Path.package list -> Resolve.Names.declaration -> bool

val list_shown_declarations :
  Resolve.Names.lookups -> Path.package list -> Resolve.Names.declaration list
