(** The type checker's entry point: loading a build's packages and gathering every stage's
    diagnostics. *)

module Manifest = Manifest

val diagnostics : Query.context -> Path.module_ -> Diagnostic.t list
(** Every diagnostic of a file, from the lexer to the package checks, in its offsets and in order.
*)

val file_diagnostics : (Path.module_, Diagnostic.t list) Query.query
(** {!diagnostics} as a query, which the database keeps current and saves. *)

(** What only a package's code shows to be wrong with its manifest. *)
type manifest_problem = Package_checks.manifest_problem =
  | Not_a_capability of { dependency : string; name : string }
      (** A grant's entry that names no capability *)
  | Unused of string
      (** A dependency that nothing in the package uses, which is told only of a package whose code
          all checks *)

val manifest_problems : (string, manifest_problem list) Query.query
(** A package's, by its name. *)

val manifest_sentence : package:string -> manifest_problem -> string

val code_packages : (string, string list) Query.query
(** The packages a package's code uses, its tests apart, by the package's name. A dependency that is
    not among them is one only its tests use. *)
