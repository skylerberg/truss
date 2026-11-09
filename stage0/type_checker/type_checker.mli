(** The type checker's entry point: loading a build's packages and gathering every stage's
    diagnostics. See TYPECHECKER.md, "Structure". *)

module Manifest = Manifest

val diagnostics : Query.context -> Path.module_ -> Diagnostic.t list
(** Every diagnostic of a file, from the lexer to the package checks, in its offsets and in order.
*)

val file_diagnostics : (Path.module_, Diagnostic.t list) Query.query
(** {!diagnostics} as a query, which the database keeps current and saves. *)
