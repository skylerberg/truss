val source : (Path.file, Source.t) Query.query
val modules : (Path.package, Path.module_ list) Query.query
val files : (Path.module_, Path.file list) Query.query
val dependencies : (Path.package, Manifest.dependency list) Query.query
val dependency_names : (Path.package, Path.package list) Query.query
val split_module : Query.context -> string list -> Path.module_ option
val module_exists : (Path.module_, bool) Query.query
