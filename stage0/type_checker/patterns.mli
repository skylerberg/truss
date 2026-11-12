(** Exhaustiveness and reachability of patterns. *)

val diagnostics : Query.context -> Path.module_ -> Diagnostic.t list
(** Every pattern error of a file, in its offsets and in order. *)
