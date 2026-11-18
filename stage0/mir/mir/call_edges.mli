type lookups = { interface : Interface.Lookups.t; mir : Parts.lookups }

type resolution = {
  target : Path.t option;
  evidence : Core.evidence option;
  supplied : Path.t list Lazy.t;
}

val resolve_callee : Interface.Lookups.t -> Types.substitution -> 'operand Core.target -> resolution

val list_code_supplied_by_function_value :
  Interface.Lookups.t -> Types.substitution -> Path.t -> Types.instantiation -> Path.t list

val list_code_supplied_by_conversion :
  Interface.Lookups.t -> Types.substitution -> Types.ty -> Types.trait_reference -> Path.t list

val list_code_supplied_to_generics :
  Interface.Lookups.t ->
  ?instance:Types.substitution ->
  Types.generic list ->
  Types.substitution ->
  Path.t list

val resolve_node : lookups -> Path.t -> Types.substitution -> Path.t
val list_impl_methods : Interface.Lookups.t -> Path.t -> Path.t list
val list_path_edges : lookups -> Path.t -> Path.t list
val list_implementations : lookups -> calling_package:Path.package -> Path.t -> Path.t list
