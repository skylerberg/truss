(** Exhaustiveness and reachability of patterns. *)

val diagnostics : Query.context -> Path.file -> Diagnostic.t list
(** Every pattern error of a file, in its offsets and in order. *)
