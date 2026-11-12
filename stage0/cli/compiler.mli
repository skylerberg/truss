type build = Development | Release

val target : unit -> Memory_layout.target
val create : ?sanitize:bool -> ?checks:bool -> Project.t -> build -> Compile.t
val test_results : unit -> Compile.results
