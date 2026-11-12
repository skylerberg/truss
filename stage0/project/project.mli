(** A project's files as inputs, and what follows from them as queries.

    A root is a tree of files: the project being worked on, the standard library, a registry
    package's files, or a package given by itself. *)

(** {1 Inputs} *)

val roots : (unit, string list) Query.input

val tree : (string, string list) Query.input
(** The paths of a root's files. *)

val text : (string * string, string) Query.input
(** A file's text, by its root and its path. *)

val unavailable : (string, string) Query.input
(** Why a registry package's files could not be had, by their hash. *)

(** {1 Roots and paths} *)

val project_root : string
val standard_root : string
val registry_root : string -> string
val package_root : Path.package -> string
val lock_file : string
val manifest_file : string -> string
val module_path : directory:string -> Path.module_ -> string

(** {1 One root} *)

type layout = {
  packages : (string * Manifest.package) list;  (** Each package's directory and manifest *)
  modules : (string * string * Path.module_) list;
      (** Each module's file, its package's directory, and the module *)
  problems : string list;
  time_limit : int;
}

val layout : (string, layout) Query.query
(** What a root's manifests and paths give: its packages, each module file's module, and what is
    wrong with a manifest by itself. It reads the tree and the manifests, and no module's text, so
    an edit to a module leaves it as it was. Manifests of another project are left out: under a root
    whose own manifest has a [[project]] table, a directory whose manifest has one too, with
    everything below it, and under a root without one, which is a project of one package, every
    other directory with a manifest. *)

(** {1 The build} *)

type selection = {
  selected : Registry.Selection.package list;
  missing : (Path.package * Registry.Version.t * string) list;
      (** Packages whose files are not inputs yet: each one's name, version, and hash *)
  failed : string list;  (** The hashes of packages whose files could not be had *)
  lock_problems : string list;
  lock_fix : string option;  (** The lock file the manifests give, when the one written is another *)
}

val selection : (unit, selection) Query.query
(** The registry packages of the build: what the project's packages depend on that is no package of
    the project, at the versions the lock file and their own records give. A package whose files are
    not inputs is missing: the database fetches it and sets them, which reaches this result. *)

type place = { root : string; directory : string; manifest : Manifest.package }

val place : (Path.package, place option) Query.query
(** Where a package of the build is, by its name. A project's package takes the place of any other
    of its name, and a root given by itself, such as the standard library's, that of a registry
    package. *)

type package = {
  name : Path.package;
  dependencies : Manifest.dependency list;
  modules : Path.module_ list;
  usize_bits : int;
}

val package : (Path.package, package option) Query.query
(** A package: what its manifest says, and its modules. *)

val module_text : (Path.module_, string option) Query.query
(** A module's text, [None] for a module that no package has. *)

val problems : (unit, string list) Query.query
(** What reading the project's manifests and lock file shows to be wrong, each as its file and
    sentences. *)

val registry : (unit, (Path.package * Registry.Version.t * string) list) Query.query
(** The registry packages of the build, in order of name: each one's name, its version, and the hash
    of its files. *)
