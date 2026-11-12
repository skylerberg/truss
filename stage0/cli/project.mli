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
  mutable files : (Path.module_ * string) list;
}

val opened : Database.session list ref
val module_files : Database.session -> package list -> (Path.module_ * string) list
val load : string -> t
val package : t -> package
val is_own : t -> Path.module_ -> bool
val manifest_problems : t -> (string * Path.package * Type_checker.manifest_problem) list
val reload : t -> unit
val modules : t -> Path.module_ list
val program_modules : t -> Path.module_ list
val file : t -> Path.module_ -> string
val selected : t -> string list -> Path.module_ list
val parsed : t -> Path.module_ -> Workspace.file
val source : t -> Path.module_ -> Source.t
val shown_workspace_path : t -> string -> string
val write_file : string -> string -> unit
val reachable : Database.dependencies -> Path.t -> (Path.t, unit) Hashtbl.t
