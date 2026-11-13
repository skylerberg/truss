type build = Development | Release

val configure_c_flags : string option -> unit
val lowering_only : Database.session -> Query.context -> Compile.t
val create : ?checks:bool -> Project.t -> build -> Compile.t
val results : unit -> Compile.results
