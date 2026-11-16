val find_head : Types.ty -> Path.t option
val list_impls_for_type : Lookups.t -> Path.t -> Path.package -> (Path.t * Path.t) list

val list_impls_of_trait_for_type :
  Lookups.t -> trait:Path.t -> type_:Path.t -> Path.package -> Path.t list

val list_impls_of_trait : Lookups.t -> trait:Path.t -> Path.package -> Path.t list
val derive_interface : Lookups.t -> type_:Path.t -> trait:Path.t -> Types.impl_interface option
val make_impl_substitution : Lookups.t -> Path.t -> Types.substitution option

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

val no_bounds : bounds

val list_required_bounds :
  Types.generic list -> Types.substitution -> (Types.ty * Types.trait_reference) list

val implements :
  Lookups.t ->
  bounds:bounds ->
  ?depth:int ->
  ?checks_conditions:bool ->
  Types.ty ->
  Types.trait_reference ->
  evidence option

val find_declaring_type_trait :
  Lookups.t -> base:Types.ty -> Types.trait_reference -> string -> Types.trait_reference

val find_declaring_capability_trait :
  Lookups.t -> base:Types.ty -> Types.trait_reference -> string -> Types.trait_reference

val project_associated_type :
  Lookups.t ->
  bounds:bounds ->
  ?defining:Path.t list ref ->
  Types.ty ->
  Types.trait_reference ->
  string ->
  Types.ty option

val project_capability_set :
  Lookups.t ->
  bounds:bounds ->
  ?depth:int ->
  Types.ty ->
  Types.trait_reference ->
  string ->
  Types.capability_set

val normalize_capabilities :
  Lookups.t -> bounds:bounds -> ?depth:int -> Types.capability_set -> Types.capability_set

val normalize : Lookups.t -> bounds:bounds -> ?defining:Path.t list ref -> Types.ty -> Types.ty
val read_signature : Lookups.t -> Path.t -> Types.signature option
val is_copyable : Lookups.t -> bounds:bounds -> Types.ty -> bool
val is_plain : Lookups.t -> bounds:bounds -> Types.ty -> bool
val is_view : Lookups.t -> bounds:bounds -> Types.ty -> bool
val holds_function : Lookups.t -> bounds:bounds -> Types.ty -> bool
val list_contents : Lookups.t -> bounds:bounds -> Types.ty -> Properties.contents
