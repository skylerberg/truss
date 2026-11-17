val check : Interface.Lookups.t -> Resolve.Names.key -> Core.t -> unit
val check_derived : Interface.Lookups.t -> Path.t -> Core.t -> unit
val list_violations : Interface.Lookups.t -> Resolve.Names.key -> Core.t -> string list

val check_file :
  Interface.Lookups.t -> find_core:(Resolve.Names.key -> Core.t option) -> Path.file -> int

val show_callee : Core.callee -> string
