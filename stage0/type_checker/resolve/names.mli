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

type visibility = Private | Internal | Public | Public_opaque
type key = { module_ : Path.module_; path : Path.t; ordinal : int }
type declaration = { key : key; kind : kind; visibility : visibility; generic : bool }
type place = { file : Path.file; base : int }

val show_key : key -> string
val extract_signature_name : Syntax.signature -> Syntax.name
val classify_receiver : Syntax.parameter list -> Path.receiver

type entry = { name : string; kind : named; visibility : visibility; generic : bool }

val is_public : visibility -> bool

type law_proof_name = { trait : Path.t; law : string; type_head : Path.t }

val derived_methods : Well_known.method_ list
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
  list_syntax_errors : key -> Source.Definition_span.t list;
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

val resolve_used_module : lookups -> from:Path.module_ -> Syntax.path -> Path.module_
val list_transitive_dependencies : lookups -> Path.package -> Path.package list
val is_visible_package : lookups -> from:Path.module_ -> Path.package -> bool
val is_visible_module : lookups -> from:Path.module_ -> Path.module_ -> bool
val find_definition : lookups -> Path.t -> (key * Syntax.definition) option

type generic_kind = Type_kind | Value_kind

val find_syntax_error : lookups -> key -> Parts.part -> Diagnostic.reported option
val is_broken : lookups -> key -> Parts.part -> bool
val list_builtin_generics : Intrinsic.builtin -> (string * generic_kind) list
val find_generics : lookups -> Path.t -> (string * generic_kind) list option

type 'visible lookup = Visible of 'visible | Hidden of (Path.t * visibility) | Absent

module Scope : sig
  val extract_last_name : Path.module_ -> string
  val is_type_kind : named -> bool
  val is_value_kind : named -> bool
  val is_visible : from:Path.module_ -> Path.module_ -> visibility -> bool
  val is_restricted_module : from:Path.module_ -> Path.module_ -> bool
  val restricted_module_message : string
  val describe_path_start : Path.module_ -> string

  type module_lookup =
    | Found_module of Path.module_
    | Restricted_module
    | Ambiguous_module of Path.module_ * Path.module_
    | No_module of string
    | No_package of string

  val lookup_module :
    lookups ->
    from:Path.module_ ->
    imports:(string * Path.module_) list ->
    string ->
    string list ->
    module_lookup

  val make_top_path : Path.module_ -> string -> Path.t

  val lookup_in :
    lookups ->
    from:Path.module_ ->
    Path.module_ ->
    string ->
    is_kind:(named -> bool) ->
    (entry * Path.t) lookup

  val find_bare_type : lookups -> from:Path.module_ -> string -> (entry * Path.t) option
end

val lookup_member : lookups -> from:Path.module_ -> Path.t -> Path.t lookup
val choose_visible : 'visible lookup list -> 'visible lookup
val collect_visible : ('key * 'visible lookup) list -> ('key * 'visible) list lookup
val describe_hidden : Path.t -> visibility -> string
val list_visible_traits_declaring : lookups -> from:Path.module_ -> string -> Path.t list

val list_members_visible_to_package :
  lookups -> package:Path.package -> Path.t -> string -> key list

val find_kind : lookups -> Path.t -> named option
