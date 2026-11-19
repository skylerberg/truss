type capability = Prelude of string | Full_path of { module_names : string list; name : string }

val prelude_capabilities : string list
val prelude_capability_module : Path.module_
val make_capability : module_names:string list -> string -> capability
val parse_capability : string -> capability option
val show_capability : capability -> string
val compare_capability : capability -> capability -> int
