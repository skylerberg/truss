(** The checks that look at more than one definition of a package. *)

type placed = { module_ : Path.module_; diagnostic : Diagnostic.t }
(** A diagnostic in the file of the module that holds it, in that file's offsets. *)

val diagnostics : Query.context -> Path.module_ -> Diagnostic.t list
(** The package's errors in one file, in order. *)

(** An error in a package's manifest that only its code shows. *)
type manifest_problem =
  | Not_a_capability of { dependency : Path.package; name : string }
      (** A grant's entry that names no capability *)
  | Unused of Path.package
      (** A dependency that nothing in the package uses, which is told only of a package whose code
          all checks *)

val manifest_problems : (Path.package, manifest_problem list) Query.query
(** A package's, by its name. *)

val manifest_sentence : package:Path.package -> manifest_problem -> string

val code_packages : (Path.package, Path.package list) Query.query
(** The packages a package's code uses, its tests apart, by the package's name. *)
