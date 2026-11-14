(** The checks that look at more than one definition of a package. *)

type placed = { file : Path.file; diagnostic : Diagnostic.t }
(** A diagnostic in the file that holds it, in that file's offsets. *)

val diagnostics : Query.context -> Path.file -> Diagnostic.t list
(** The package's errors in one file, in order. *)

type manifest_problem =
  | Not_a_capability of { dependency : Path.package; name : string }
      (** A grant's entry that names no capability *)
  | Unused of Path.package

val manifest_problems : (Path.package, manifest_problem list) Query.query
val manifest_sentence : package:Path.package -> manifest_problem -> string
val code_packages : (Path.package, Path.package list) Query.query
