type build = Development | Release

val lowering_only : Pipeline.t -> Path.package list -> Compile.t

val create :
  ?checks:bool -> Pipeline.t -> Database.snapshot -> Path.package list -> build -> Compile.t
