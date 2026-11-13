(** The rules on use: every variable is used, and no code is unreachable. *)

val diagnostics : Query.context -> Path.file -> Diagnostic.t list
(** Every error of use in a file, in its offsets and in order. *)
