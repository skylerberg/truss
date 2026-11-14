val checked :
  Database.session ->
  Path.package list ->
  Path.file list ->
  Path.file ->
  Diagnostic.t list * Diagnostic.span Prover.state list

val diagnostics :
  Database.session -> Path.package list -> Path.file list -> Path.file -> Diagnostic.t list

val holes_reached :
  Database.session -> Path.package list -> Path.t -> (Path.t * string * int * int) list
