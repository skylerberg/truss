type package = { owner : string option; name : string }

val package_parts : package -> string list
val show_package : package -> string
val compare_package : package -> package -> int
val parse_names : string -> string list option
val parse_package : string -> package option

type module_ = { package : package; modules : string list }

val split_module : is_package:(package -> bool) -> string list -> module_ option
val module_parts : module_ -> string list
val show_module : module_ -> string

type file = { module_ : module_; name : string }

val file_names : file -> string list
val show_file : file -> string

type receiver = Static | Read | Mut | Own

val show_receiver : receiver -> string

type t =
  | Top of { module_ : module_; name : string }
  | Method of { owner : t; name : string; receiver : receiver }
  | Member_constant of { owner : t; name : string }
  | Impl of { module_ : module_; trait : reference; for_type : t }
  | Derived of { type_ : t; trait : t }
  | Test of { module_ : module_; name : string }
  | Law_proof of { module_ : module_; trait : reference; law : string; for_type : t }

and reference = { path : t; arguments : argument list; associated : (string * argument) list }

and argument =
  | Named of reference
  | Parameter of string
  | Any of reference
  | Count of Z.t
  | Constant of t

val standard_package : package
val standard_module : string list -> module_
val standard : string list -> string -> t
val package : t -> package
val show : t -> string
val compare : t -> t -> int
val equal : t -> t -> bool
val hash : t -> int

module Map : Map.S with type key = t
module Set : Set.S with type elt = t
