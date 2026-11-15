type t

val check : Pipeline.t -> Database.snapshot -> Path.package list -> Path.file list -> t
val diagnostics : t -> Path.file -> Diagnostic.t list
val states : t -> Path.file -> Diagnostic.span Prover.state list
val holes : Database.snapshot -> Path.package list -> t -> Path.t -> (string * int * int) list
