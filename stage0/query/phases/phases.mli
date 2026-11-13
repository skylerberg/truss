(** The compiler's phases, in order: each reads the ones before it. A stage declares its queries in
    one of them. *)

val project : Query.phase
(** A project's packages, their modules and text, and the registry packages of its build *)

val syntax : Query.phase
(** A file's tokens and trees *)

val declarations : Query.phase
(** Each file's and package's declarations, and finding a definition by name *)

val resolution : Query.phase
(** The meaning of each name in a definition *)

val interfaces : Query.phase
(** Signatures, shapes, constants, and the [impl]s found for a type *)

val bodies : Query.phase
(** Checked bodies, and the facts found in them *)

val checks : Query.phase
(** The rules that span a package *)

val proofs : Query.phase
(** Each definition's obligations, as the solver's queries, and the call graph *)

val verdicts : Query.phase
(** Whether each definition's obligations hold, from the solver's answers *)

val diagnostics : Query.phase
(** Every stage's diagnostics for a file *)

val lowering : Query.phase
(** Each instance's LIR *)

val linking : Query.phase
(** Each instance's references, and the hash of its own code *)

val recursion : Query.phase
(** Which instances reach themselves *)

val keys : Query.phase
(** The key of everything an instance can reach *)
