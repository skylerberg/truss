type stage = Resolve | Interface | Infer | Patterns | Usage | Ownership | Package_checks

val diagnostics : Query.context -> Path.file -> Diagnostic.t list
val file_diagnostics : (Path.file, Diagnostic.t list) Query.query

type manifest_problem = Package_checks.manifest_problem =
  | Not_a_capability of { dependency : Path.package; name : string }
  | Unused of Path.package

val manifest_problems : (Path.package, manifest_problem list) Query.query
val manifest_sentence : package:Path.package -> manifest_problem -> string
val code_packages : (Path.package, Path.package list) Query.query

module For_testing : sig
  val through : stage -> Query.context -> Path.file -> Diagnostic.t list
end
