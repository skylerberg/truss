type t = { prefix : string list; last : string; member : string option }

val parse : string -> t

type target =
  | Package of Path.package
  | Module of Path.module_
  | Definition of Path.t
  | Trait_member of { member : Path.t; impl : Path.t }

val resolve : Resolve.Names.lookups -> Path.package list -> t -> target list
val explain_missing : Resolve.Names.lookups -> Path.package list -> string -> string
val is_shown : Path.package list -> Resolve.Names.declaration -> bool

val list_array_methods_of_list :
  Resolve.Names.declaration list -> Path.t -> Resolve.Names.declaration list

val list_shown_declarations :
  Resolve.Names.lookups -> Path.package list -> Resolve.Names.declaration list
