val copyable_trait : Path.t
val plain_trait : Path.t
val storable_trait : Path.t

val trait_substitution :
  Types.trait_interface -> self:Types.ty -> Types.trait_reference -> Types.substitution

val bound_closure :
  Lookups.t -> self:Types.ty -> Types.trait_reference -> Types.trait_reference list

val known_bounds :
  Lookups.t ->
  bounds:(Types.parameter -> Types.trait_reference list) ->
  Types.ty ->
  Types.trait_reference list

type property = Copyable | Plain | View | Holds_function
type occurrence = Environment.occurrence = In_place | Indirect | Function_input

val through : occurrence -> occurrence -> occurrence

type recursion = { recursive : Types.ty; occurrence : occurrence; defining : Path.t list }
type contents = { contained : (Types.ty * occurrence) list; recursions : recursion list }

val fields_named : package:Path.package -> Types.type_interface -> Path.t list

val component_facts :
  Lookups.t -> (Path.t * Types.type_interface) list -> (Path.t * Environment.type_facts) list

val has :
  Lookups.t ->
  bounds:(Types.parameter -> Types.trait_reference list) ->
  normalize:(Types.ty -> Types.ty) ->
  property ->
  Types.ty ->
  bool

val storable :
  Lookups.t ->
  bounds:(Types.parameter -> Types.trait_reference list) ->
  normalize:(Types.ty -> Types.ty) ->
  Types.ty ->
  bool

val contents : Lookups.t -> normalize:(Types.ty -> Types.ty * Path.t list) -> Types.ty -> contents
