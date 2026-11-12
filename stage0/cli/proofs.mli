val checked :
  Project.t ->
  Path.module_ list ->
  Path.module_ ->
  Diagnostic.t list * Diagnostic.span Prover.state list

val diagnostics : Project.t -> Path.module_ list -> Path.module_ -> Diagnostic.t list
val holes_reached : Project.t -> Path.t -> Path.t list
