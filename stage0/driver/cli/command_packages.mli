val manifest_name : string
val write_file : string -> string -> unit
val load : string -> Workspace.snapshot * Path.package list
val load_current : unit -> Workspace.snapshot * Path.package list
val retake : Workspace.snapshot -> Workspace.snapshot
val load_worktree : unit -> Workspace.snapshot * Path.package list
val require_one : Path.package list -> Path.package
val locate_directory : Workspace.snapshot -> Path.package -> string
val locate_file : Workspace.snapshot -> Path.file -> string
val list_files : Workspace.snapshot -> Path.package list -> Path.file list
val list_modules : Workspace.snapshot -> Path.package list -> Path.module_ list
val list_program_packages : Workspace.snapshot -> Path.package list -> Path.package list

val list_manifest_problems :
  Workspace.snapshot ->
  Database.t ->
  Path.package list ->
  (string * Path.package * Database.manifest_problem) list

val select_files : Workspace.snapshot -> Path.package list -> string list -> Path.file list
val read_source : Workspace.snapshot -> Path.package list -> Path.file -> Source.t
val show_file : Workspace.snapshot -> Path.package list -> Path.file -> string
