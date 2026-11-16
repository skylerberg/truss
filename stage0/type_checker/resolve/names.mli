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
type unresolved_name = Type_path of Syntax.path | Count_name of Syntax.name

type unresolved_header = {
  item : Syntax.definition Syntax.item;
  imports : (string * Path.module_) list;
  names : unresolved_name list;
}

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
  unresolved_headers : Path.file -> unresolved_header list;
  package_declarations : Path.package -> declaration list;
  definition : key -> Syntax.definition option;
  text : key -> string option;
  spans : key -> Source.Definition_span.t array option;
  recovered : key -> Source.Definition_span.t list option;
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

val recovery_report : lookups -> key -> Parts.part -> Diagnostic.reported option
val is_broken : lookups -> key -> Parts.part -> bool
val generics_of : lookups -> Path.t -> (string * generic_kind) list option

type name_lookup = Found_name of entry * Path.t | Hidden_name of entry | No_name

val find_in :
  lookups -> from:Path.module_ -> Path.module_ -> string -> is_kind:(named -> bool) -> name_lookup

val find_bare_type : lookups -> from:Path.module_ -> string -> (entry * Path.t) option
val kind_of : lookups -> Path.t -> named option

type namespace

val namespace :
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

val changes : namespace -> namespace -> change list

val of_namespaces :
  namespace:(Path.package -> namespace) ->
  module_exists:(Path.module_ -> bool) ->
  split_module:(string list -> Path.module_ option) ->
  dependency_names:(Path.package -> Path.package list) ->
  lookups
