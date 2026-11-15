type root = Project | Standard | Registry of string | Package of Path.package

val roots : (unit, root list) Query.input
val tree : (root, string list) Query.input
val text : (root * string, string) Query.input
val unavailable : (string, string) Query.input
val package_root : Path.package -> root
val lock_file : string
val manifest_file : string -> string
val file_path : directory:string -> Path.file -> string
val parent : string -> string
val segments : string -> string list
val package_directory : is_package:(string -> bool) -> string -> string option

type source_file = { path : string; directory : string; file : Path.file }
type problem = { file : string; line : int option; message : string }

val show_problem : problem -> string

type layout = {
  packages : (string * Manifest.package) list;
  files : source_file list;
  problems : problem list;
  time_limit_ms : int;
}

val layout : (root, layout) Query.query

type selection = {
  selected : Registry.Selection.package list;
  missing : (Path.package * Registry.Version.t * string) list;
  failed : string list;
  lock_problems : problem list;
  lock_fix : string option;
}

val selection : (unit, selection) Query.query

type place = { root : root; directory : string; manifest : Manifest.package }

val place : (Path.package, place option) Query.query

type package = {
  name : Path.package;
  dependencies : Manifest.dependency list;
  modules : Path.module_ list;
  files : Path.file list;
}

val package : (Path.package, package option) Query.query
val file_text : (Path.file, string option) Query.query
val problems : (unit, problem list) Query.query
val registry : (unit, (Path.package * Registry.Version.t * string) list) Query.query
