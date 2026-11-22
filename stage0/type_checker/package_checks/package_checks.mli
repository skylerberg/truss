module Lookups = Lookups

type placed = { key : Resolve.Names.key; diagnostic : Diagnostic.in_definition }

val describe_unused_dependency : package:Path.package -> Path.package -> string

type check =
  | Sealed of Resolve.Names.key
  | Impl of Resolve.Names.key
  | Type of Resolve.Names.key
  | Instantiations
  | Tests
  | Unexported
  | Dependencies

val list_checks : Resolve.Names.declaration list -> check list
val list_uses : Core.t -> Path.t list
val list_instantiations : Resolve.Names.key -> Core.t -> (Path.t * bool) list
val is_checked_for_instantiation : Resolve.Names.declaration -> bool

type outcome = Placed of placed list | Unused_dependencies of Path.package list

val run : Lookups.t -> Path.package -> check -> outcome
