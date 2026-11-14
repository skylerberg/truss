(** The checks of a build's packages: every stage that reports diagnostics before the prover, from
    the lexer to the package checks, run in order and gathered by file. *)

(** The stages, in the order they run. *)
type stage = Resolve | Interface | Infer | Patterns | Usage | Ownership | Package_checks

val diagnostics : Query.context -> Path.file -> Diagnostic.t list

val file_diagnostics : (Path.file, Diagnostic.t list) Query.query
(** {!diagnostics} as a query, which the database keeps current and saves. *)

type manifest_problem = Package_checks.manifest_problem =
  | Not_a_capability of { dependency : Path.package; name : string }
      (** A grant's entry that names no capability *)
  | Unused of Path.package

val manifest_problems : (Path.package, manifest_problem list) Query.query
val manifest_sentence : package:Path.package -> manifest_problem -> string
val code_packages : (Path.package, Path.package list) Query.query

(** The stages, for their tests. *)
module For_testing : sig
  val through : stage -> Query.context -> Path.file -> Diagnostic.t list
end
