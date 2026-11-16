type t

val check : Database.t -> Workspace.snapshot -> Path.package list -> Path.file list -> t
val list_diagnostics : t -> Path.file -> Diagnostic.t list
val list_states : t -> Path.file -> Source.span Prover.state list
val list_holes : Workspace.snapshot -> Path.package list -> t -> Path.t -> (string * int * int) list
