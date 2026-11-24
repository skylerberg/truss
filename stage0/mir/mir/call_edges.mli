type lookups = { interface : Interface.Lookups.t; mir : Parts.lookups }
type resolution = { target : Path.t option; supplied : Path.t list Lazy.t }

val resolve_callee : Interface.Lookups.t -> Types.substitution -> 'operand Core.target -> resolution

type supplier = Call | Named_function of Path.t | Provide
type edge = Calls of Path.t | Supplies of { supplier : supplier; code : Path.t list }

val list_statement_edges : Interface.Lookups.t -> Types.substitution -> Tree.statement -> edge list

val list_code_supplied_to_generics :
  Interface.Lookups.t ->
  ?instance:Types.substitution ->
  Types.generic list ->
  Types.substitution ->
  Path.t list

type dependency_kind = Read | Direct_call | Supplied of supplier
type omitted = Field of string | Argument of string

type dependency = {
  path : Path.t;
  kind : dependency_kind;
  origin : Core.origin;
  omitted : omitted option;
}

val list_dependencies : lookups -> Types.substitution -> Tree.t -> dependency list
val list_invariant_cycles : lookups -> Path.t -> (dependency * Path.t) list
val resolve_node : lookups -> Path.t -> Types.substitution -> Path.t
val list_path_edges : lookups -> Path.t -> Path.t list
