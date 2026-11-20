module Lookups = Lookups

type placed = { key : Resolve.Names.key; diagnostic : Diagnostic.in_definition }

val make_mentions : Resolve.Names.key -> Core.t -> packages:Path.package list -> Lookups.mentions
val describe_unused_dependency : package:Path.package -> Path.package -> string

type check =
  | Sealed of Resolve.Names.key
  | Impl of Resolve.Names.key
  | Type of Resolve.Names.key
  | Constant of Resolve.Names.key
  | Instantiations
  | Tests
  | Unexported
  | Dependencies

val list_checks : Resolve.Names.declaration list -> check list

type outcome = Placed of placed list | Unused_dependencies of Path.package list

val run : Lookups.t -> Path.package -> check -> outcome
