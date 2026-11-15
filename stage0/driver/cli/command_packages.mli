val manifest_name : string
val write_file : string -> string -> unit
val load : string -> Database.snapshot * Path.package list
val current : unit -> Database.snapshot * Path.package list
val worktree : unit -> Database.snapshot * Path.package list
val one : Path.package list -> Path.package
val directory : Database.snapshot -> Path.package -> string
val path : Database.snapshot -> Path.file -> string
val files : Database.snapshot -> Path.package list -> Path.file list
val modules : Database.snapshot -> Path.package list -> Path.module_ list
val program_packages : Database.snapshot -> Path.package list -> Path.package list

val manifest_problems :
  Database.snapshot ->
  Pipeline.t ->
  Path.package list ->
  (string * Path.package * Package_checks.manifest_problem) list

val selected : Database.snapshot -> Path.package list -> string list -> Path.file list
val source : Database.snapshot -> Path.package list -> Path.file -> Source.t
val shown_workspace_path : Database.snapshot -> Path.package list -> string -> string
