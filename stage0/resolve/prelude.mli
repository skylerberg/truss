val types : (string * Path.module_) list
val variants : (string * string) list
val find_type : string -> Path.module_ option
val find_variant : string -> (Path.t * string) option
val names : string list
