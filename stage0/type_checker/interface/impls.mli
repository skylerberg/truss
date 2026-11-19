val find_head : Types.ty -> Path.t option
val list_impls_for_type : Lookups.t -> Path.t -> Path.package -> (Path.t * Path.t) list

val list_impls_of_trait_for_type :
  Lookups.t -> trait:Path.t -> type_:Path.t -> Path.package -> Path.t list

val list_impls_of_trait : Lookups.t -> trait:Path.t -> Path.package -> Path.t list
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

type evidence =
  | From_impl of { impl : Path.t; substitution : Types.substitution }
  | From_bound
  | From_any
  | Built_in
  | Accepted of Types.ty

type through_any = Callable | Has_generics | Names_self

val classify_through_any : Lookups.t -> trait:Path.t -> Types.trait_method -> through_any

type bounds = Types.parameter -> Types.trait_reference list

val list_no_bounds : bounds

val list_required_bounds :
  Types.generic list -> Types.substitution -> (Types.ty * Types.trait_reference) list

val find_evidence :
  Lookups.t ->
  list_bounds:bounds ->
  ?depth:int ->
  ?checks_conditions:bool ->
  Types.ty ->
  Types.trait_reference ->
  evidence option

val check_recursion_depth : depth:int -> Types.ty -> Types.trait_reference -> unit
val select_impl : Lookups.t -> Types.ty -> Types.trait_reference -> Types.impl_interface option

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

val project_capability_set :
  Lookups.t ->
  list_bounds:bounds ->
  ?depth:int ->
  Types.ty ->
  Types.trait_reference ->
  string ->
  Types.capability_set

val normalize_capabilities :
  Lookups.t -> list_bounds:bounds -> ?depth:int -> Types.capability_set -> Types.capability_set

val decide_condition :
  Lookups.t -> list_bounds:bounds -> ?depth:int -> Types.condition -> Types.condition option

val normalize : Lookups.t -> list_bounds:bounds -> ?defining:Path.t list ref -> Types.ty -> Types.ty

module Conformance : sig
  val find_implementation_of : Lookups.t -> Types.impl_interface -> implementation option

  val list_impl_bounds :
    Types.impl_interface -> list_bounds:bounds -> Types.parameter -> Types.trait_reference list

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
val read_scope : Lookups.t -> Resolve.Names.key -> Environment.scope

type declaring_clause =
  | Own_uses
  | Impl_uses
  | Associated_capability_set of { name : string; is_defined : bool; is_named : bool }

type capability_declaration =
  | Declared_by of declaring_clause
  | Fixed_by_trait of { trait : Types.trait_reference; method_name : string }

val find_capability_declaration :
  Lookups.t -> Path.t -> Types.capability -> capability_declaration option

val show_declaring_clause : declaring_clause -> string -> string

val decide_property :
  Properties.property -> Lookups.t -> list_bounds:bounds -> Types.ty -> Properties.decision

val is_copyable : Lookups.t -> list_bounds:bounds -> Types.ty -> bool
val is_plain : Lookups.t -> list_bounds:bounds -> Types.ty -> bool
val is_view : Lookups.t -> list_bounds:bounds -> Types.ty -> bool
val holds_function : Lookups.t -> list_bounds:bounds -> Types.ty -> bool
val collect_contents : Lookups.t -> list_bounds:bounds -> Types.ty -> Properties.contents
