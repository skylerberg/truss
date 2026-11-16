type build = Development | Release

val lowering_only : Database.t -> Path.package list -> Compile.t
val create : Database.t -> Workspace.snapshot -> Path.package list -> build -> Compile.t
