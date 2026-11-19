val read : string -> string
val write : string -> string -> unit
val write_all : Unix.file_descr -> string -> unit
val write_atomically : string -> string -> unit
val make_directory : string -> unit
val remove : string -> unit
val write_directory : string -> (string * string) list -> unit
val write_directory_atomically : string -> (string * string) list -> unit
val join_path : string -> string -> string
val find_relative_path : root:string -> string -> string option
val is_inside : directory:string -> string -> bool
val find_parent : string -> string option
