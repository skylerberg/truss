val check : Interface.Lookups.t -> Resolve.Names.key -> Core.t -> unit
val check_derived : Interface.Lookups.t -> Path.t -> Core.t -> unit

val check_file :
  Interface.Lookups.t -> core:(Resolve.Names.key -> Core.t option) -> Path.file -> int

val callee_name : Core.callee -> string
