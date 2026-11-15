module Lookups = Lookups

type placed = { file : Path.file; diagnostic : Diagnostic.t }

type manifest_problem =
  | Not_a_capability of { dependency : Path.package; name : string }
  | Unused of Path.package

val manifest_sentence : package:Path.package -> manifest_problem -> string

val used_packages :
  Resolve.resolved -> evidence_packages:Path.package list -> Core.t -> Path.package list

val checks : Lookups.t -> Path.package -> (unit -> placed list) list
val grant_problems : Lookups.t -> Path.package -> manifest_problem list
val unused_dependencies : Lookups.t -> Path.package -> manifest_problem list
val code_packages : Lookups.t -> Path.package -> Path.package list
