exception Recursion_limit of string

val recursion_limit : int

val list_bound_closure_over :
  find_requirements:(Path.t -> (Types.generic list * Types.trait_reference list) option) ->
  self:Types.ty ->
  Types.trait_reference ->
  Types.trait_reference list

val list_bound_closure :
  Lookups.t -> self:Types.ty -> Types.trait_reference -> Types.trait_reference list

val find_trait_declaring_type :
  Lookups.t -> base:Types.ty -> Types.trait_reference -> string -> Types.trait_reference option

val find_trait_declaring_capability_set :
  Lookups.t -> base:Types.ty -> Types.trait_reference -> string -> Types.trait_reference option

val list_known_bounds :
  Lookups.t ->
  list_bounds:(Types.parameter -> Types.trait_reference list) ->
  Types.ty ->
  Types.trait_reference list

val list_rigid_members :
  Lookups.t ->
  list_bounds:(Types.parameter -> Types.trait_reference list) ->
  Types.ty ->
  Language.Builtin_type.t list

type property = Copyable | Plain | View | Holds_function

val show_property : property -> string

type occurrence = Environment.occurrence = In_place | Indirect | Function_input

val compose_occurrences : occurrence -> occurrence -> occurrence

type recursion = { recursive : Types.ty; occurrence : occurrence; defining : Path.t list }
type contents = { contained : (Types.ty * occurrence) list; recursions : recursion list }

val list_field_type_paths : package:Path.package -> Types.type_interface -> Path.t list

val compute_component_facts :
  Lookups.t -> (Path.t * Types.type_interface) list -> (Path.t * Environment.type_facts) list

type decision = Holds | Fails | Depends_on of Types.ty

val decide_property :
  Lookups.t ->
  list_bounds:(Types.parameter -> Types.trait_reference list) ->
  normalize:(Types.ty -> Types.ty) ->
  property ->
  Types.ty ->
  decision

val decide_storable :
  Lookups.t ->
  list_bounds:(Types.parameter -> Types.trait_reference list) ->
  normalize:(Types.ty -> Types.ty) ->
  Types.ty ->
  decision

val collect_contents :
  Lookups.t -> normalize:(Types.ty -> Types.ty * Path.t list) -> Types.ty -> contents
