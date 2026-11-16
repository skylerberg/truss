exception Recursion_limit of string

val recursion_limit : int

val make_trait_substitution :
  Types.trait_interface -> self:Types.ty -> Types.trait_reference -> Types.substitution

val list_bound_closure :
  Lookups.t -> self:Types.ty -> Types.trait_reference -> Types.trait_reference list

val find_trait_declaring_type :
  Lookups.t -> base:Types.ty -> Types.trait_reference -> string -> Types.trait_reference option

val find_trait_declaring_capability_set :
  Lookups.t -> base:Types.ty -> Types.trait_reference -> string -> Types.trait_reference option

val list_known_bounds :
  Lookups.t ->
  bounds:(Types.parameter -> Types.trait_reference list) ->
  Types.ty ->
  Types.trait_reference list

type property = Copyable | Plain | View | Holds_function
type occurrence = Environment.occurrence = In_place | Indirect | Function_input

val compose_occurrences : occurrence -> occurrence -> occurrence

type recursion = { recursive : Types.ty; occurrence : occurrence; defining : Path.t list }
type contents = { contained : (Types.ty * occurrence) list; recursions : recursion list }

val list_field_type_paths : package:Path.package -> Types.type_interface -> Path.t list

val compute_component_facts :
  Lookups.t -> (Path.t * Types.type_interface) list -> (Path.t * Environment.type_facts) list

val has_property :
  Lookups.t ->
  bounds:(Types.parameter -> Types.trait_reference list) ->
  normalize:(Types.ty -> Types.ty) ->
  property ->
  Types.ty ->
  bool

val is_storable :
  Lookups.t ->
  bounds:(Types.parameter -> Types.trait_reference list) ->
  normalize:(Types.ty -> Types.ty) ->
  Types.ty ->
  bool

val collect_contents :
  Lookups.t -> normalize:(Types.ty -> Types.ty * Path.t list) -> Types.ty -> contents
