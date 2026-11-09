(** The rules on use: every variable is used, and no code is unreachable. See TYPECHECKER.md,
    "Unreachable code". *)

val definition_diagnostics : (Resolve.Names.key, Diagnostic.t list) Query.query
(** A definition's errors of use, in its own offsets. *)

val diagnostics : Query.context -> Path.module_ -> Diagnostic.t list
(** Every error of use in a file, in its offsets and in order. *)
