type build = Development | Release

val make_lowering_compiler : Database.t -> Path.package list -> Compile.t
val create : Database.t -> Workspace.snapshot -> Path.package list -> build -> Compile.t
