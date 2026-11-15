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

type type_head = { type_name : string; generics : string list }

val show_type_head : type_head -> string

type receiver = Static | Read | Mut | Own

val show_receiver : receiver -> string

type t =
  | Top of { module_ : module_; name : string }
  | Method of { owner : t; name : string; receiver : receiver }
  | Member_constant of { owner : t; name : string }
  | Impl of { module_ : module_; trait : string; for_type : type_head }
  | Derived of { type_ : t; trait : t }
  | Test of { module_ : module_; name : string }
  | Law_proof of { module_ : module_; trait : string; law : string; for_type : type_head }

val standard_package : package
val standard_module : string list -> module_
val standard : string list -> string -> t
val package : t -> package
val show : t -> string
val compare : t -> t -> int
val equal : t -> t -> bool

module Map : Map.S with type key = t
module Set : Set.S with type elt = t
