exception Cannot_run of string

val cannot_run : ('a, unit, string, 'b) format4 -> 'a
val manifest_name : string
val normalize : string -> string
val relative : from:string -> string -> string
val real : string -> string
val shown : string -> string

type package = { name : Path.package; directory : string }

type t = {
  session : Database.session;
  context : Query.context;
  packages : package list;
  mutable files : (Path.file * string) list;  (** Each file of [packages], with its absolute path *)
}

val opened : Database.session list ref
val file_paths : Database.session -> package list -> (Path.file * string) list
val load : string -> t
val package : t -> package
val is_own : t -> Path.module_ -> bool
val manifest_problems : t -> (string * Path.package * Checks.manifest_problem) list
val reload : t -> unit
val files : t -> Path.file list
val modules : t -> Path.module_ list
val program_files : t -> Path.file list
val path : t -> Path.file -> string

val selected : t -> string list -> Path.file list
(** The files in the paths, each a file or a directory, or every file when there are none. *)

val parsed : t -> Path.file -> Workspace.file
val source : t -> Path.file -> Source.t
val shown_workspace_path : t -> string -> string
val write_file : string -> string -> unit
