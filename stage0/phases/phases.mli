(** The compiler's phases, in order: each reads the ones before it. A stage declares its queries in
    one of them. *)

val syntax : Query.phase
(** A file's tokens and trees *)

val declarations : Query.phase
(** What each file and package declares, and finding a definition by name *)

val resolution : Query.phase
(** What each name in a definition means *)

val interfaces : Query.phase
(** Signatures, shapes, constants, and the [impl]s found for a type *)

val bodies : Query.phase
(** Checked bodies, and what is found in them *)

val checks : Query.phase
(** The rules that span a package *)

val proofs : Query.phase
(** Each definition's obligations, as the solver's queries, and the call graph *)

val verdicts : Query.phase
(** Whether each definition's obligations hold, from the solver's answers *)

val diagnostics : Query.phase
(** Every stage's diagnostics for a file *)

val lowering : Query.phase
(** What each instance compiles to *)

val linking : Query.phase
(** What each instance refers to, and the hash of its own code *)

val recursion : Query.phase
(** Which instances reach themselves *)

val keys : Query.phase
(** The key of everything an instance can reach *)
