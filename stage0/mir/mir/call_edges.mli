type lookups = { interface : Interface.Lookups.t; mir : Parts.lookups }

type assumption = {
  assumer : Path.t;
  parameter : Types.parameter option;
  assumed : Types.ty * Types.trait_reference;
}

type dictionary = {
  parameter : Types.parameter;
  argument : Types.ty;
  methods : Path.t list;
  assumed_methods : Path.t list;
  assumptions : assumption list;
}

type resolution = {
  target : Path.t option;
  callee : Path.t option;
  dictionaries : dictionary list Lazy.t;
}

val list_dictionary_methods : dictionary -> Path.t list
val resolve_callee : Interface.Lookups.t -> Types.substitution -> 'operand Core.target -> resolution
val find_instance : lookups -> Path.t -> Types.substitution
val find_code : lookups -> Path.t -> Tree.t option

type higher_order_argument = Dictionary | Function_value of Path.t | Handler
type edge = Calls of Path.t | Passes of { argument : higher_order_argument; code : Path.t list }

val list_statement_edges : Interface.Lookups.t -> Types.substitution -> Tree.statement -> edge list

val list_code_passed_to_self :
  Interface.Lookups.t -> trait:Path.t -> Types.substitution -> Path.t list

val list_code_passed_to_generics :
  Interface.Lookups.t ->
  ?instance:Types.substitution ->
  Types.generic list ->
  Types.substitution ->
  Path.t list

type dependency_kind = Read | Direct_call | Passed of higher_order_argument

val locate_call : Tree.statement -> Core.origin

type dependency = {
  path : Path.t;
  kind : dependency_kind;
  origin : Core.origin;
  default : Path.t option;
}

val list_dependencies : lookups -> Types.substitution -> Tree.t -> dependency list
val list_contract_dependencies : lookups -> Path.t -> dependency list
val list_inherited_contract_dependencies : lookups -> Path.t -> dependency list
val list_invariant_dependencies : lookups -> Path.t -> dependency list
val list_potential_dependencies : lookups -> Path.t -> dependency list

type type_use = { type_ : Types.ty; origin : Core.origin option }
type instance_use = { used : type_use; dependencies : Path.t list }

val list_instance_uses : lookups -> Path.t -> instance_use list

val list_law_proofs :
  lookups ->
  Path.package ->
  Types.trait_reference ->
  Types.ty ->
  (string * Resolve.Names.key * Types.substitution) list

type assumed_laws = {
  impl : Path.t;
  trait : Types.trait_reference;
  type_ : Types.ty;
  origin : Core.origin option;
  is_assumed_by_the_callee : bool;
}

val list_assumed_laws : lookups -> Path.t -> assumed_laws list
val list_assumed_paths : lookups -> Path.t -> Path.t list
val resolve_node : lookups -> Path.t -> Types.substitution -> Path.t
val list_path_edges : lookups -> Path.t -> Path.t list
val is_specification_only : lookups -> Path.t -> bool
val has_abort_site : lookups -> Path.t -> bool

val body_may_abort :
  lookups ->
  Types.substitution ->
  lambdas:Tree.body array ->
  Tree.body ->
  may_abort:(Path.t -> bool) ->
  bool

val list_callees_that_run : lookups -> Path.t -> Path.t list
val list_instance_field_types : Interface.Lookups.t -> Types.ty -> Types.ty list
