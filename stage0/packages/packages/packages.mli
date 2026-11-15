val source : (Path.file, Source.t) Query.query
(** A file's text, with its table of lines. Raises [Not_found] if it has no text. *)

val modules : (Path.package, Path.module_ list) Query.query

val files : (Path.module_, Path.file list) Query.query
(** A module's files, in order. *)

val dependencies : (Path.package, Manifest.dependency list) Query.query
(** A package's dependencies, each with its grants. *)

val split_module : Query.context -> string list -> Path.module_ option
val module_exists : (Path.module_, bool) Query.query
