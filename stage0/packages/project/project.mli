type root = Project | Registry of string

type files = {
  find_tree : root -> string list option;
  find_text : root -> string -> string option;
  find_unavailable_reason : string -> string option;
}

val lock_file : string
val make_manifest_path : string -> string
val make_file_path : directory:string -> Path.file -> string
val find_package_directory : is_package:(string -> bool) -> string -> string option

type source_file = { path : string; directory : string; file : Path.file }
type problem = { file : string; line : int option; message : string }

val show_problem : problem -> string

type layout = {
  packages : (string * Manifest.package) list;
  files : source_file list;
  problems : problem list;
  time_limit_ms : int;
}

type selection = {
  selected : Registry.Selection.package list;
  missing : (Path.package * Registry.Version.t * string) list;
  failed : string list;
  lock_problems : problem list;
  lock_fix : string option;
}

type place = { root : root; directory : string; manifest : Manifest.package }

type package = {
  name : Path.package;
  dependencies : Manifest.dependency list;
  files : (Path.file * string) list;
}

type t = {
  own : layout;
  selection : selection;
  places : (Path.package * place) list;
  packages : package list;
  problems : problem list;
}

val of_files : files -> t
