type build = Development | Release

val target : unit -> Memory_layout.target
val lowering_only : Database.session -> Query.context -> Compile.t
val create : ?sanitize:bool -> ?checks:bool -> Project.t -> build -> Compile.t
val test_results : unit -> Compile.results
