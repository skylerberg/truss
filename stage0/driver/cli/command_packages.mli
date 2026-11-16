val manifest_name : string
val write_file : string -> string -> unit
val load : string -> Workspace.snapshot * Path.package list
val current : unit -> Workspace.snapshot * Path.package list
val retake : Workspace.snapshot -> Workspace.snapshot
val worktree : unit -> Workspace.snapshot * Path.package list
val one : Path.package list -> Path.package
val directory : Workspace.snapshot -> Path.package -> string
val path : Workspace.snapshot -> Path.file -> string
val files : Workspace.snapshot -> Path.package list -> Path.file list
val modules : Workspace.snapshot -> Path.package list -> Path.module_ list
val program_packages : Workspace.snapshot -> Path.package list -> Path.package list

val list_manifest_problems :
  Workspace.snapshot ->
  Database.t ->
  Path.package list ->
  (string * Path.package * Database.manifest_problem) list

val selected : Workspace.snapshot -> Path.package list -> string list -> Path.file list
val source : Workspace.snapshot -> Path.package list -> Path.file -> Source.t
val shown_workspace_path : Workspace.snapshot -> Path.package list -> string -> string
