type package = { owner : string option; name : string }

val list_package_parts : package -> string list
val show_package : package -> string
val compare_package : package -> package -> int
val parse_names : string -> string list option
val parse_package : string -> package option

type module_ = { package : package; modules : string list }

val split_module : is_package:(package -> bool) -> string list -> module_ option
val list_module_parts : module_ -> string list
val show_module : module_ -> string

type file = { module_ : module_; name : string }

val list_file_names : file -> string list
val show_package_directory : package -> string
val show_file : file -> string

type receiver = Static | Instance of Language.Mode.t

val show_receiver : receiver -> string

type t =
  | Top of { module_ : module_; name : string }
  | Method of { owner : t; name : string; receiver : receiver }
  | Member_constant of { owner : t; name : string }
  | Default of { owner : t; variant : string option; name : string }
  | Impl of { module_ : module_; trait : reference; for_type : t }
  | Derived of { type_ : t; trait : t }
  | Test of { module_ : module_; name : string }
  | Law_proof of { module_ : module_; trait : reference; law : string; for_type : t }
  | Unresolved of { file : file; names : string list }

and reference = { path : t; arguments : argument list; associated : (string * argument) list }
and argument = Named of reference | Parameter of string | Count of Z.t | Constant of t

val standard_package : package
val make_standard_module : string list -> module_
val make_standard_path : string list -> string -> t
val make_capability_method : t -> string -> t
val is_entry_point : t -> bool
val locate_package : t -> package
val is_resolved : t -> bool
val show : t -> string
val show_name : t -> string
val compare : t -> t -> int
val equal : t -> t -> bool
val hash : t -> int

module Map : Map.S with type key = t

type key = { module_ : module_; path : t; ordinal : int }
