type placed = { file : Path.file; diagnostic : Diagnostic.t }

val diagnostics : Query.context -> Path.file -> Diagnostic.t list

type manifest_problem =
  | Not_a_capability of { dependency : Path.package; name : string }
  | Unused of Path.package

val manifest_problems : (Path.package, manifest_problem list) Query.query
val manifest_sentence : package:Path.package -> manifest_problem -> string
val code_packages : (Path.package, Path.package list) Query.query
