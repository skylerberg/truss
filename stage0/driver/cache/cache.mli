type t

val locate_default_directory : unit -> (string, string) result
val make_root : string -> (string, string) result
val open_ : string -> (t, string) result
val directory : t -> string
val make_objects_directory : t -> string
val make_package_databases_directory : t -> string
val make_packages_directory : t -> string
val make_programs_directory : t -> string
val collect : t -> budget:int -> unit
