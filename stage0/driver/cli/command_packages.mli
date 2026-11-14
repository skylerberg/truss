val manifest_name : string
val write_file : string -> string -> unit
val load : string -> Database.session * Path.package list
val current : unit -> Database.session * Path.package list
val worktree : unit -> Database.session * Path.package list
val one : Path.package list -> Path.package
val directory : Database.session -> Path.package -> string
val path : Database.session -> Path.file -> string
val files : Database.session -> Path.package list -> Path.file list
val modules : Database.session -> Path.package list -> Path.module_ list
val program_files : Database.session -> Path.package list -> Path.file list

val selected : Database.session -> Path.package list -> string list -> Path.file list
(** The files in the paths, each a file or a directory, or every file when there are none. *)

val source : Database.session -> Path.package list -> Path.file -> Source.t
val shown_workspace_path : Database.session -> Path.package list -> string -> string
