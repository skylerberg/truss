(** The type checker's entry point: loading a build's packages and gathering every stage's
    diagnostics. *)

(** The stages, in the order they run. *)
type stage = Resolve | Interface | Infer | Patterns | Usage | Ownership | Package_checks

val diagnostics : Query.context -> Path.file -> Diagnostic.t list
(** Every diagnostic of a file, from the lexer to the package checks, in its offsets and in order.
*)

val file_diagnostics : (Path.file, Diagnostic.t list) Query.query
(** {!diagnostics} as a query, which the database keeps current and saves. *)

(** An error in a package's manifest that only its code shows. *)
type manifest_problem = Package_checks.manifest_problem =
  | Not_a_capability of { dependency : Path.package; name : string }
      (** A grant's entry that names no capability *)
  | Unused of Path.package
      (** A dependency that nothing in the package uses, which is told only of a package whose code
          all checks *)

val manifest_problems : (Path.package, manifest_problem list) Query.query
(** A package's, by its name. *)

val manifest_sentence : package:Path.package -> manifest_problem -> string

val code_packages : (Path.package, Path.package list) Query.query
(** The packages a package's code uses, its tests apart, by the package's name. A dependency that is
    not among them is one only its tests use. *)

(** The type checker's own stages, for their tests. *)
module For_testing : sig
  val through : stage -> Query.context -> Path.file -> Diagnostic.t list
  (** The diagnostics of a file's definitions from the stages up to and including one, in the order
      the stages run, for tests of a stage that leave the later ones out. *)
end
