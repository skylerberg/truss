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
  module_ : Path.module_;
  path : Path.t;
  ordinal : int;
  kind : kind;
  visibility : Syntax.visibility;
  generic : bool;
}

type key = { module_ : Path.module_; path : Path.t; ordinal : int }
type place = { file : Path.file; base : int }

val key_of : declaration -> key
val show_key : key -> string
val spell_path : Syntax.path -> string
val signature_name : Syntax.signature -> Syntax.name
val receiver : Syntax.parameter list -> Path.receiver
val last_name : Path.module_ -> string

type entry = { name : string; kind : named; visibility : Syntax.visibility; generic : bool }

module String_map : Map.S with type key = String.t

val is_type_kind : named -> bool
val is_value_kind : named -> bool
val is_public : Syntax.visibility -> bool
val visible : from:Path.module_ -> Path.module_ -> Syntax.visibility -> bool

type law_proof_name = { trait : Path.t; law : string; type_head : Path.t }

val derivable : Path.t -> bool

type lookups = {
  find : Path.module_ -> string -> entry option;
  entries : Path.module_ -> entry list;
  imports : key -> (string * Path.module_) list;
  module_exists : Path.module_ -> bool;
  split_module : string list -> Path.module_ option;
  dependency_names : Path.package -> Path.package list;
  key : Path.t -> key option;
  declaration : key -> declaration option;
  declarations : Path.module_ -> declaration list;
  declarations_in : Path.file -> declaration list;
  package_declarations : Path.package -> declaration list;
  definition : key -> Syntax.definition option;
  text : key -> string option;
  spans : key -> Source.Definition_span.t array option;
  place : key -> place option;
  container : key -> key option;
  contained : key -> key list;
  members : Path.t -> string -> key list;
  traits_declaring : Path.package -> string -> Path.t list;
  impls : Path.package -> ((Path.t * Path.t) * Path.t) list;
  impls_of_type : Path.package -> Path.t -> (Path.t * Path.t) list;
  impls_of_trait : Path.package -> Path.t -> Path.t list;
  law_proofs : Path.package -> law_proof_name -> key list;
}

type module_lookup =
  | Found_module of Path.module_ * [ `Import of string | `Package ]
  | Ambiguous_module of Path.module_ * Path.module_
  | No_module of string

val used_module : lookups -> from:Path.module_ -> Syntax.path -> Path.module_
val is_visible_module : lookups -> from:Path.module_ -> Path.module_ -> bool

val lookup_module :
  lookups ->
  from:Path.module_ ->
  imports:(string * Path.module_) list ->
  string list ->
  module_lookup

val definition_of_path : lookups -> Path.t -> (key * Syntax.definition) option
val law_parameters : lookups -> Path.t -> string -> string list option

type generic_kind = Type_kind | Value_kind | Capability_kind

val generics_of : lookups -> Path.t -> (string * generic_kind) list option
val kind_of : lookups -> Path.t -> named option

type module_names
type module_namespace
type package_index

val index_entries : Syntax.file list -> module_names
val build_module_namespace : lookups -> (Path.file * Syntax.file * string) list -> module_namespace
val build_package_index : module_namespace list -> package_index
val empty_package_index : package_index

type change =
  | Entry of Path.module_ * string
  | Imports of key
  | Declaration of key
  | Tree of key
  | Positions of key
  | Text of key
  | Place of key
  | Container of key
  | Contained of key
  | Module_declarations of Path.module_
  | File_declarations of Path.file
  | Module_index of Path.module_
  | Package_declarations
  | Members of Path.t * string
  | Traits_declaring of string
  | Impl_index
  | Impls_of_type of Path.t
  | Impls_of_trait of Path.t
  | Law_proofs of law_proof_name

val list_entry_changes : Path.module_ -> module_names option -> module_names option -> change list

val list_module_changes :
  Path.module_ -> module_namespace option -> module_namespace option -> change list

val list_index_changes : package_index -> package_index -> change list

val make_lookups :
  entries:(Path.module_ -> module_names option) ->
  namespace:(Path.module_ -> module_namespace option) ->
  index:(Path.package -> package_index) ->
  module_exists:(Path.module_ -> bool) ->
  split_module:(string list -> Path.module_ option) ->
  dependency_names:(Path.package -> Path.package list) ->
  lookups
