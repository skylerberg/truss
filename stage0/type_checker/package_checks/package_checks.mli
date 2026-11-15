module Lookups = Lookups

type placed = { key : Resolve.Names.key; diagnostic : Syntax.diagnostic }

type manifest_problem =
  | Not_a_capability of { dependency : Path.package; name : string }
  | Unused of Path.package

val manifest_sentence : package:Path.package -> manifest_problem -> string

val used_packages :
  Resolve.resolved -> evidence_packages:Path.package list -> Core.t -> Path.package list

type check =
  | Sealed of Resolve.Names.key
  | Impl of Resolve.Names.key
  | Type of Resolve.Names.key
  | Instantiations
  | Tests
  | Grants
  | Dependencies
  | Code_packages

val checks : Resolve.Names.declaration list -> check list

type outcome =
  | Placed of placed list
  | Problems of manifest_problem list
  | Packages of Path.package list

val run : Lookups.t -> Path.package -> check -> outcome
