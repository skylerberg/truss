module Lookups = Lookups

type placed = { key : Resolve.Names.key; diagnostic : Diagnostic.in_definition }

val describe_unused_dependency : package:Path.package -> Path.package -> string

type use = Used | Unused of { is_named : bool }

type check =
  | Sealed of Resolve.Names.key
  | Impl of Resolve.Names.key
  | Type of Resolve.Names.key
  | Instantiation of Resolve.Names.key
  | Test of Resolve.Names.key
  | Unexported of Resolve.Names.key * use
  | Dependency of Path.package

val list_uses : Core.t -> Path.t list
val list_instantiations : Resolve.Names.key -> Core.t -> (Path.t * bool) list

val find_growing_cycles :
  Lookups.t -> Resolve.Names.declaration list -> (Resolve.Names.key * bool) list

val classify_uses :
  Lookups.t -> Resolve.Names.declaration list -> (Resolve.Names.declaration * use) list

type outcome = Placed of placed list | Dependency_used of bool

val run : Lookups.t -> Path.package -> check -> outcome
