type t

val check : Database.t -> Workspace.snapshot -> Path.package list -> Database.proof_scope -> t
val list_diagnostics : t -> Path.file -> Diagnostic.t list
val list_states : t -> Path.file -> Database.proof_state list

val list_holes :
  Workspace.snapshot -> t -> reached:Path.t list -> (string * int * int * Path.t list) list
