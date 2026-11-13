val checked :
  Project.t -> Path.file list -> Path.file -> Diagnostic.t list * Diagnostic.span Prover.state list

val diagnostics : Project.t -> Path.file list -> Path.file -> Diagnostic.t list

type hole = { definition : Path.t; file : Path.file; offset : int }

val holes_reached : Project.t -> Path.t -> hole list
