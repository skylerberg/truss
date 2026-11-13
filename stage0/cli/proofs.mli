val checked :
  Project.t -> Path.file list -> Path.file -> Diagnostic.t list * Diagnostic.span Prover.state list

val diagnostics : Project.t -> Path.file list -> Path.file -> Diagnostic.t list
val holes_reached : Project.t -> Path.t -> (Path.t * string * int * int) list
