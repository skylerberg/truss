type build = Development | Release

val make_lowering_requests : Database.t -> Path.package list -> Compile.requests
val create : Database.t -> Workspace.snapshot -> Path.package list -> build -> Compile.t
