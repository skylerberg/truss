(** Exhaustiveness and reachability of patterns. *)

val definition_diagnostics : (Resolve.Names.key, Diagnostic.t list) Query.query
(** A definition's pattern errors, in its own offsets: arms not covered, unreachable arms and
    alternatives, and refutable patterns where only irrefutable ones may go. *)

val diagnostics : Query.context -> Path.module_ -> Diagnostic.t list
(** Every pattern error of a file, in its offsets and in order. *)
