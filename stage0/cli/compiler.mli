type build = Development | Release

val lowering_only : Database.session -> Query.context -> Compile.t
val create : ?checks:bool -> Project.t -> build -> Compile.t
val results : unit -> Compile.results
