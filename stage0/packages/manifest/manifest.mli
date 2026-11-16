type dependency = { package : Path.package; capabilities : string list }
type package = { name : Path.package; truss : string option; dependencies : dependency list }
type t = { package : package option; time_limit_seconds : int option }

val default_time_limit_seconds : int

exception Malformed of { line : int; message : string }

val parse : string -> t
val has_project_table : string -> bool
val add_dependency : string -> Path.package -> string
val remove_dependency : string -> Path.package -> string
val is_valid_name : string -> bool
val parse_name : string -> Path.package option
val truss_version : string
val toolchain_builds : string -> bool
