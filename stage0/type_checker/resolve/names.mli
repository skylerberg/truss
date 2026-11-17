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

val convert_named : named -> kind
val show_kind : kind -> string

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

val make_key : declaration -> key
val show_key : key -> string
val extract_signature_name : Syntax.signature -> Syntax.name
val classify_receiver : Syntax.parameter list -> Path.receiver
val extract_last_name : Path.module_ -> string

type entry = {
  name : string;
  kind : named;
  visibility : Syntax.visibility;
  takes_type_arguments : bool;
}

module String_map : Map.S with type key = String.t

val is_type_kind : named -> bool
val is_value_kind : named -> bool
val is_public : Syntax.visibility -> bool
val is_visible : from:Path.module_ -> Path.module_ -> Syntax.visibility -> bool

type law_proof_name = { trait : Path.t; law : string; type_head : Path.t }

val is_derivable : Path.t -> bool

type lookups = {
  find : Path.module_ -> string -> entry option;
  list_entries : Path.module_ -> entry list;
  list_imports : key -> (string * Path.module_) list;
  module_exists : Path.module_ -> bool;
  split_module : string list -> Path.module_ option;
  list_dependency_names : Path.package -> Path.package list;
  find_key : Path.t -> key option;
  read_declaration : key -> declaration;
  list_declarations : Path.module_ -> declaration list;
  list_declarations_in : Path.file -> declaration list;
  list_package_declarations : Path.package -> declaration list;
  read_definition : key -> Syntax.definition;
  read_text : key -> string;
  read_spans : key -> Source.Definition_span.t array;
  list_recovered : key -> Source.Definition_span.t list;
  read_place : key -> place;
  find_container : key -> key option;
  list_contained : key -> key list;
  list_members : Path.t -> string -> key list;
  list_traits_declaring : Path.package -> string -> Path.t list;
  list_impls : Path.package -> ((Path.t * Path.t) * Path.t) list;
  list_impls_of_type : Path.package -> Path.t -> (Path.t * Path.t) list;
  list_impls_of_trait : Path.package -> Path.t -> Path.t list;
  list_law_proofs : Path.package -> law_proof_name -> key list;
}

type module_lookup =
  | Found_module of Path.module_ * [ `Import of string | `Package ]
  | Ambiguous_module of Path.module_ * Path.module_
  | No_module of string

val resolve_used_module : lookups -> from:Path.module_ -> Syntax.path -> Path.module_
val list_visible_packages : lookups -> Path.package -> Path.package list
val list_transitive_dependencies : lookups -> Path.package -> Path.package list
val is_visible_module : lookups -> from:Path.module_ -> Path.module_ -> bool

val lookup_module :
  lookups ->
  from:Path.module_ ->
  imports:(string * Path.module_) list ->
  string ->
  string list ->
  module_lookup

val find_definition : lookups -> Path.t -> (key * Syntax.definition) option
val find_law_parameters : lookups -> Path.t -> string -> string list option

type generic_kind = Type_kind | Value_kind | Capability_kind

val find_recovery_report : lookups -> key -> Parts.part -> Diagnostic.reported option
val is_broken : lookups -> key -> Parts.part -> bool
val find_generics : lookups -> Path.t -> (string * generic_kind) list option

type name_lookup = Found_name of entry * Path.t | Hidden_name of entry | No_name

val lookup_in :
  lookups -> from:Path.module_ -> Path.module_ -> string -> is_kind:(named -> bool) -> name_lookup

val find_bare_type : lookups -> from:Path.module_ -> string -> (entry * Path.t) option
val find_kind : lookups -> Path.t -> named option

type namespace

val build_namespace :
  lookups ->
  Path.package ->
  (Path.module_ * (Path.file * Syntax.file * string) list) list ->
  namespace

val empty_namespace : namespace

type change =
  | Entry of Path.module_ * string
  | Entries of Path.module_
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
  | Package_declarations
  | Members of Path.t * string
  | Traits_declaring of string
  | Impl_index
  | Impls_of_type of Path.t
  | Impls_of_trait of Path.t
  | Law_proofs of law_proof_name

val list_changes : namespace -> namespace -> change list

val of_namespaces :
  read_namespace:(Path.package -> namespace) ->
  module_exists:(Path.module_ -> bool) ->
  split_module:(string list -> Path.module_ option) ->
  list_dependency_names:(Path.package -> Path.package list) ->
  lookups
