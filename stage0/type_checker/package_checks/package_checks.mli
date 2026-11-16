module Lookups = Lookups

type placed = { key : Resolve.Names.key; diagnostic : Diagnostic.in_definition }

val describe_unused_dependency : package:Path.package -> Path.package -> string

val list_used_packages :
  Resolve.resolved -> evidence_packages:Path.package list -> Core.t -> Path.package list

type check =
  | Sealed of Resolve.Names.key
  | Impl of Resolve.Names.key
  | Type of Resolve.Names.key
  | Constant of Resolve.Names.key
  | Instantiations
  | Tests
  | Dependencies

val list_checks : Resolve.Names.declaration list -> check list

type outcome = Placed of placed list | Unused_dependencies of Path.package list

val run : Lookups.t -> Path.package -> check -> outcome
