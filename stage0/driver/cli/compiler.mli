type build = Development | Release

val lowering_only : Pipeline.t -> Path.package list -> Compile.t
val create : Pipeline.t -> Workspace.snapshot -> Path.package list -> build -> Compile.t
