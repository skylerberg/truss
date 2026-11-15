val head : Types.ty -> Path.t option
val derivable : Path.t -> bool
val index : (Path.package, ((Path.t * Path.t) * Path.t) list) Query.query
val impls_for : Query.context -> Path.t -> Path.package -> (Path.t * Path.t) list
val impls_in : (Path.t * Path.t * Path.package, Path.t list) Query.query
val cursor_trait : Path.t
val impl_interface : Query.context -> Path.t -> Types.impl_interface option
val trait_substitution : Query.context -> Path.t -> Types.substitution option

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

val through_any : trait:Path.t -> Types.trait_method -> through_any
val copyable_path : Path.t

type bounds = Types.parameter -> Types.trait_reference list

val required : Types.generic list -> Types.substitution -> (Types.ty * Types.trait_reference) list

val implements :
  Query.context ->
  bounds:bounds ->
  ?depth:int ->
  ?conditions:bool ->
  Types.ty ->
  Types.trait_reference ->
  evidence option

val associated_type :
  Query.context ->
  bounds:bounds ->
  ?defining:Path.t list ref ->
  Types.ty ->
  Types.trait_reference ->
  string ->
  Types.ty option

val capability_set :
  Query.context ->
  bounds:bounds ->
  ?depth:int ->
  Types.ty ->
  Types.trait_reference ->
  string ->
  Types.capability_set

val normalize_capabilities :
  Query.context -> bounds:bounds -> ?depth:int -> Types.capability_set -> Types.capability_set

val normalize : Query.context -> bounds:bounds -> ?defining:Path.t list ref -> Types.ty -> Types.ty
val signature : Query.context -> Path.t -> Types.signature option
val copyable : Query.context -> bounds:bounds -> Types.ty -> bool
val plain : Query.context -> bounds:bounds -> Types.ty -> bool
val is_view : Query.context -> bounds:bounds -> Types.ty -> bool
val holds_function : Query.context -> bounds:bounds -> Types.ty -> bool
val contents : Query.context -> bounds:bounds -> Types.ty -> Properties.contents
