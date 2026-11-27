val find_head : Types.ty -> Path.t option
val list_impls_for_type : Lookups.t -> Path.t -> Path.package -> (Path.t * Path.t) list

val list_impls_of_trait_for_type :
  Lookups.t -> trait:Path.t -> type_:Path.t -> Path.package -> Path.t list

val list_impls_of_trait : Lookups.t -> trait:Path.t -> Path.package -> Path.t list
val derived_generics : Types.generic list -> Types.trait_reference -> Types.generic list
val derive_interface : Lookups.t -> type_:Path.t -> trait:Path.t -> Types.impl_interface option

type implementation = {
  impl : Types.impl_interface;
  trait : Types.trait_interface;
  substitution : Types.substitution;
}

val find_implementation : Lookups.t -> Path.t -> implementation option

type implemented_method = {
  implementation : implementation;
  declared : Types.trait_method;
  declaration : Path.t;
}

val find_implemented_method : Lookups.t -> Path.t -> implemented_method option

val find_trait_restated_by :
  Lookups.t ->
  self:Types.ty ->
  Types.trait_reference ->
  Types.restated_method ->
  Types.trait_reference option

val is_same_trait : Types.trait_reference -> Types.trait_reference -> bool

type added_clauses = {
  restating_method : Path.t;
  substitution : Types.substitution;
  holds_when : Types.condition;
}

val list_added_clauses : Lookups.t -> Path.t -> added_clauses list

val match_type :
  variables:Types.parameter list ->
  Types.substitution ->
  Types.ty ->
  Types.ty ->
  Types.substitution option

val match_arguments :
  variables:Types.parameter list ->
  Types.substitution ->
  Types.argument list ->
  Types.argument list ->
  Types.substitution option

type solution = Evidence of Types.evidence | Built_in | Accepted of Types.ty
type bounds = Properties.Bounds.t

val list_no_bounds : bounds

type required_bound = {
  parameter : Types.parameter;
  argument : Types.ty;
  bound : Types.trait_reference;
}

val list_required_bounds_of_parameters :
  Types.generic list -> Types.substitution -> required_bound list

val list_required_bounds :
  Types.generic list -> Types.substitution -> (Types.ty * Types.trait_reference) list

val list_associated_type_bounds :
  Lookups.t -> Types.impl_interface -> Types.substitution -> (Types.ty * Types.trait_reference) list

type method_code =
  | Method_of_impl of { impl : Path.t; substitution : Types.substitution }
  | Declaration_for_view

val locate_method :
  Lookups.t -> Types.evidence -> name:string -> receiver:Path.receiver -> method_code option

type obligation =
  | Provides of Types.trait_method
  | Bounds_associated_type of { name : string; chosen : Types.ty; bound : Types.trait_reference }
  | Requires of Types.trait_reference

val list_obligations :
  Lookups.t ->
  list_bounds:bounds ->
  Types.trait_interface ->
  Types.impl_interface ->
  self:Types.ty ->
  obligation list

val find_evidence :
  Lookups.t ->
  list_bounds:bounds ->
  ?depth:int ->
  ?checks_conditions:bool ->
  Types.ty ->
  Types.trait_reference ->
  solution option

val resolve_evidence :
  Lookups.t ->
  Types.substitution ->
  self_type:Types.ty ->
  trait:Types.trait_reference ->
  Types.evidence ->
  Types.evidence

val check_recursion_depth : depth:int -> Types.ty -> Types.trait_reference -> unit

type matched_impl = {
  impl_path : Path.t;
  impl : Types.impl_interface;
  substitution : Types.substitution;
}

val list_matching_impls : Lookups.t -> Types.ty -> Types.trait_reference -> matched_impl list

val decide_property_trait :
  Lookups.t -> list_bounds:bounds -> Path.t -> Types.ty -> Properties.decision option

val list_matching_bounds :
  Lookups.t -> list_bounds:bounds -> Types.ty -> Types.trait_reference -> Types.trait_reference list

val project_associated_type :
  Lookups.t ->
  list_bounds:bounds ->
  ?defining:Path.t list ref ->
  Types.ty ->
  Types.trait_reference ->
  string ->
  Types.ty option

val normalize_capabilities :
  Lookups.t -> list_bounds:bounds -> ?depth:int -> Types.capability_set -> Types.capability_set

val decide_condition :
  Lookups.t -> list_bounds:bounds -> ?depth:int -> Types.condition -> Types.condition option

val add_condition_bounds : Lookups.t -> bounds -> Types.condition -> bounds

val implies_condition :
  Lookups.t -> list_bounds:bounds -> Types.condition -> Types.condition -> bool

val normalize : Lookups.t -> list_bounds:bounds -> ?defining:Path.t list ref -> Types.ty -> Types.ty

module Conformance : sig
  val find_implementation_of : Lookups.t -> Types.impl_interface -> implementation option
  val list_impl_bounds : Lookups.t -> Types.impl_interface -> list_bounds:bounds -> bounds

  val normalize_capabilities_in_impl :
    Lookups.t ->
    list_bounds:bounds ->
    Types.impl_interface ->
    Types.capability_set ->
    Types.capability_set

  val normalize_signature_in_impl :
    Lookups.t -> list_bounds:bounds -> implementation -> Types.signature -> Types.signature

  val make_expected_signature :
    Lookups.t -> ?written:Types.signature -> implemented_method -> Types.signature
end

val read_signature : Lookups.t -> Path.t -> Types.signature option
val read_scope : Lookups.t -> Resolve.Names.key -> Environment.known_bounds Environment.scope

type declaring_clause = Catalog.Capabilities.declaring_clause =
  | Own_uses
  | Impl_uses
  | Associated_capability_set of { name : string; is_defined : bool; is_named : bool }

type capability_declaration = Catalog.Capabilities.declaration =
  | Declared_by of declaring_clause
  | Fixed_by_trait of { trait : Types.trait_reference; method_name : string }

val find_capability_declaration :
  Lookups.t -> Path.t -> Types.capability -> capability_declaration option

val decide_property :
  Properties.property -> Lookups.t -> list_bounds:bounds -> Types.ty -> Properties.decision

val is_copyable : Lookups.t -> list_bounds:bounds -> Types.ty -> bool
val is_plain : Lookups.t -> list_bounds:bounds -> Types.ty -> bool
val is_view : Lookups.t -> list_bounds:bounds -> Types.ty -> bool
val holds_function : Lookups.t -> list_bounds:bounds -> Types.ty -> bool
val binding_may_alias : Lookups.t -> list_bounds:bounds -> Language.Mode.t -> Types.ty -> bool
val collect_contents : Lookups.t -> list_bounds:bounds -> Types.ty -> Properties.contents
