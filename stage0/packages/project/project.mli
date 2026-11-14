(** A project's files as inputs, and queries derived from them.

    A root is a tree of files: the project being worked on, the standard library, a registry
    package's files, or a package given by itself. *)

(** {1 Inputs} *)

val roots : (unit, string list) Query.input

val tree : (string, string list) Query.input
(** The paths of a root's files. *)

val text : (string * string, string) Query.input
(** A file's text, by its root and its path. *)

val unavailable : (string, string) Query.input

(** {1 Roots and paths} *)

val project_root : string
val standard_root : string
val registry_root : string -> string
val package_root : Path.package -> string
val lock_file : string
val manifest_file : string -> string

val file_path : directory:string -> Path.file -> string
(** A file's path in its root, under its package's [directory]. *)

val parent : string -> string
(** The directory a relative path is in, [""] for the root. *)

val segments : string -> string list
(** A relative path's names, none for the root. *)

val package_directory : is_package:(string -> bool) -> string -> string option
(** The package a relative directory is in: the directory itself, or the nearest directory above it,
    for which [is_package] holds. *)

(** {1 One root} *)

type layout = {
  packages : (string * Manifest.package) list;  (** Each package's directory and manifest *)
  files : (string * string * Path.file) list;
      (** Each [.truss] file's path, its package's directory, and the file of a module it is *)
  problems : string list;
  time_limit : int;
}

val layout : (string, layout) Query.query

(** {1 The build} *)

type selection = {
  selected : Registry.Selection.package list;
  missing : (Path.package * Registry.Version.t * string) list;
      (** Packages whose files are not inputs yet: each one's name, version, and hash *)
  failed : string list;
  lock_problems : string list;
  lock_fix : string option;  (** The lock file the manifests give, when the one written is another *)
}

val selection : (unit, selection) Query.query

type place = { root : string; directory : string; manifest : Manifest.package }

val place : (Path.package, place option) Query.query

type package = {
  name : Path.package;
  dependencies : Manifest.dependency list;
  modules : Path.module_ list;  (** Each directory with a [.truss] file, in order *)
  files : Path.file list;
  usize_bits : int;
}

val package : (Path.package, package option) Query.query
(** A package: its manifest's contents, its modules, and their files. *)

val file_text : (Path.file, string option) Query.query
(** A file's text, [None] for a file that no package has. *)

val problems : (unit, string list) Query.query
(** The errors in the project's manifests and lock file, each as its file and sentences. *)

val registry : (unit, (Path.package * Registry.Version.t * string) list) Query.query
(** The registry packages of the build, in order of name: each one's name, its version, and the hash
    of its files. *)
