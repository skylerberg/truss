val read : string -> string
val write : string -> string -> unit
val write_all : Unix.file_descr -> string -> unit
val write_atomically : ?durable:bool -> string -> string -> unit
val make_directory : string -> unit
val remove : string -> unit
val write_directory : string -> (string * string) list -> unit
val write_directory_atomically : string -> (string * string) list -> unit
