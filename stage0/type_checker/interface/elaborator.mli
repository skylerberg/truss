type t

val create : Lookups.t -> Resolve.resolved -> Environment.known_bounds Environment.scope -> t
val list_known_bounds : t -> Properties.Bounds.t
val find_self_type : t -> Types.ty option
val list_diagnostics : t -> Catalog.diagnostic list
val list_applications : t -> (Syntax.id * Types.application) list
val record_diagnostic : Catalog.diagnostic list ref -> Catalog.Typing.t -> Catalog.reported
val list_trait_closure : Lookups.t -> Path.t -> Path.t list
val split_part : Syntax.expression -> (string * Syntax.name list * bool) option
val find_bounded_type : t -> Syntax.expression -> Types.ty option
val elaborate_associated_expression : t -> Syntax.expression -> Types.ty option

type bound_method = {
  self_type : Types.ty;
  trait : Types.trait_reference;
  name : string;
  receiver : Path.receiver;
}

val list_bound_methods : t -> Types.ty -> string -> bound_method list
val find_operand_method : bound_method list -> bound_method option

type operand_callee =
  | Function_parameter of Syntax.name
  | Bound_method of { type_ : Syntax.expression; method_ : Syntax.name }
  | Not_a_callee

type cost_operand = {
  written : Syntax.expression;
  cost_function : Syntax.name;
  metric : Language.Metric.t;
  callee : operand_callee;
}

val list_cost_operands : t -> Syntax.expression -> cost_operand list
val elaborate_type : t -> Syntax.type_expression -> Types.ty
val elaborate_capability : t -> Syntax.capability_reference -> Types.capability list
val elaborate_mode : Syntax.mode option -> Language.Mode.t
val elaborate_condition : t -> Syntax.condition -> Types.condition
val add_condition : t -> Types.condition -> t

val elaborate_header :
  Lookups.t -> Resolve.Names.key -> (Environment.header, Catalog.diagnostic list) result

val elaborate_definition : Lookups.t -> Resolve.Names.key -> Environment.elaborated_interface
