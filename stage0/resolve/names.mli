type kind =
  | Function
  | Type
  | Trait
  | Capability
  | Constant
  | Theorem
  | Method
  | Member_constant
  | Impl
  | Test
  | Law_proof

type named = Function | Type | Trait | Capability | Constant | Theorem

val kind_of_named : named -> kind
val kind_name : kind -> string

type declaration = {
  file : Path.file;  (** Where it is written. *)
  path : Path.t;
  ordinal : int;
  index : int;
  container : int option;
  kind : kind;
  visibility : Syntax.visibility;
  generic : bool;
}

type key = { module_ : Path.module_; path : Path.t; ordinal : int }

val key_of : declaration -> key
val show_key : key -> string
val spell_path : Syntax.path -> string
val signature_name : Syntax.signature -> Syntax.name
val receiver : Syntax.parameter list -> Path.receiver
val used_module : Query.context -> from:Path.module_ -> Syntax.path -> Path.module_
val last_name : Path.module_ -> string
val module_exists : Query.context -> Path.module_ -> bool

type entry = { name : string; kind : named; visibility : Syntax.visibility; generic : bool }

val entries : (Path.module_, entry list) Query.query

module String_map : Map.S with type key = String.t

val find : (Path.module_ * String_map.key, entry option) Query.query
val is_type_kind : named -> bool
val is_value_kind : named -> bool
val is_public : Syntax.visibility -> bool
val visible : from:Path.module_ -> Path.module_ -> Syntax.visibility -> bool

type module_lookup =
  | Found_module of Path.module_ * [ `Import of string | `Package ]
  | Ambiguous_module of Path.module_ * Path.module_
  | No_module of string

val lookup_module : Query.context -> from:Path.file -> string list -> module_lookup
(** The module that the names before [::] denote in a file, through the file's imports. *)

val declarations : (Path.module_, declaration list) Query.query
(** A module's declarations, file by file. A definition's ordinal counts the earlier ones with its
    path across the module, so two files that define one name make a duplicate. *)

val declarations_in : (Path.file, declaration list) Query.query
(** The declarations written in one file, numbered as in {!declarations}. *)

module Member_map : Map.S with type key = Path.t * string

val package_declarations : (Path.package, declaration list) Query.query

val impl_types : (Path.module_, (Path.t option * Path.t) list) Query.query
(** Each [impl] of a module, with the type its head names, if it names one. *)

val traits_declaring : (Path.package * String_map.key, Path.t list) Query.query
val members : (Path.t * string, key list) Query.query

module Declaration_map : Map.S with type key = Path.t * int

val declaration_index : (Path.module_, declaration Declaration_map.t) Query.query

val file_of : (key, Path.file option) Query.query
(** The file a definition is written in. *)

val container : (key, key option) Query.query
val contained : (key, key list) Query.query
val definition : (key, Syntax.definition option) Query.query
val law_parameters : (Path.t * string, string list option) Query.query
val spans : (key, Syntax.span array option) Query.query
val base : (key, (Path.file * int) option) Query.query

val per_definition :
  Query.context -> Path.file -> (key -> Syntax.diagnostic list) -> Diagnostic.t list

val text : (key, string option) Query.query

module For_testing : sig
  val imports : (Path.file, (string * Path.module_) list) Query.query
end
