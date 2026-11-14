(** The packages of a build, as the compiler's stages see them: each package's modules, files,
    dependencies, and width of [USize], and each file's text. The project's own packages, the
    standard library, and registry packages are alike here. The driver's view, with the files'
    inputs, the manifests' layout, and the registry, is {!Project}'s. *)

val source : (Path.file, Source.t) Query.query
(** A file's text, with its table of lines. Raises [Not_found] if it has no text. *)

val modules : (Path.package, Path.module_ list) Query.query
(** A package's modules, and none for a package there is not. *)

val files : (Path.module_, Path.file list) Query.query
(** A module's files, in order. *)

val dependencies : (Path.package, Manifest.dependency list) Query.query
(** A package's dependencies, each with its grants. *)

val usize_bits : (Path.package, int) Query.query
(** The width of [USize] a package's code must hold for. *)

val exists : (Path.package, bool) Query.query
(** Whether there is a package of that name. *)

val split_module : Query.context -> string list -> Path.module_ option
(** The module that the names of a full path start with, whose package is two of them when it has an
    owner; [None] when they start with no package's name. *)

val module_exists : (Path.module_, bool) Query.query
(** Whether a package has the module, which a [use] line or a full path asks. *)
