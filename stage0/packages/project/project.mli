val roots : (unit, string list) Query.input
val tree : (string, string list) Query.input
val text : (string * string, string) Query.input
val unavailable : (string, string) Query.input
val project_root : string
val standard_root : string
val registry_root : string -> string
val package_root : Path.package -> string
val lock_file : string
val manifest_file : string -> string
val file_path : directory:string -> Path.file -> string
val parent : string -> string
val segments : string -> string list
val package_directory : is_package:(string -> bool) -> string -> string option

type source_file = { path : string; directory : string; file : Path.file }

type layout = {
  packages : (string * Manifest.package) list;
  files : source_file list;
  problems : string list;
  time_limit : int;
}

val layout : (string, layout) Query.query

type selection = {
  selected : Registry.Selection.package list;
  missing : (Path.package * Registry.Version.t * string) list;
  failed : string list;
  lock_problems : string list;
  lock_fix : string option;
}

val selection : (unit, selection) Query.query

type place = { root : string; directory : string; manifest : Manifest.package }

val place : (Path.package, place option) Query.query

type package = {
  name : Path.package;
  dependencies : Manifest.dependency list;
  modules : Path.module_ list;
  files : Path.file list;
}

val package : (Path.package, package option) Query.query
val file_text : (Path.file, string option) Query.query
val problems : (unit, string list) Query.query
val registry : (unit, (Path.package * Registry.Version.t * string) list) Query.query
