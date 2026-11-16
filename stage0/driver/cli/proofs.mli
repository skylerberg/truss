type t

val check : Pipeline.t -> Workspace.snapshot -> Path.package list -> Path.file list -> t
val diagnostics : t -> Path.file -> Diagnostic.t list
val states : t -> Path.file -> Source.span Prover.state list
val holes : Workspace.snapshot -> Path.package list -> t -> Path.t -> (string * int * int) list
