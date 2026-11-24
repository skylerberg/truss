type t

val create :
  Lookups.t ->
  Resolve.resolved ->
  spans:Source.Definition_span.t array ->
  Environment.known_bounds Environment.scope ->
  t

val read_span : t -> Syntax.id -> Source.Definition_span.t
val list_known_bounds : t -> Properties.Bounds.t
val find_self_type : t -> Types.ty option
val list_diagnostics : t -> Catalog.description list
val list_named_types : t -> (Syntax.id * Types.ty) list
val record_diagnostic : Catalog.description list ref -> Catalog.Typing.t -> Diagnostic.reported
val list_trait_closure : Lookups.t -> Path.t -> Path.t list
val find_bounded_type : t -> Syntax.expression -> Types.ty option

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
val show_path : Syntax.path -> string
val elaborate_type : t -> Syntax.type_expression -> Types.ty
val elaborate_condition : t -> Syntax.condition -> Types.condition
val add_condition : t -> Types.condition -> t

val elaborate_header :
  Lookups.t -> Resolve.Names.key -> (Environment.header, Catalog.description list) result

val elaborate_definition : Lookups.t -> Resolve.Names.key -> Environment.elaborated_interface
