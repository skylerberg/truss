module Environment = Environment
module Lookups = Lookups

module Elaborator : sig
  type t = Elaborator.t

  val create : Lookups.t -> Resolve.resolved -> Environment.known_bounds Environment.scope -> t
  val list_known_bounds : t -> Properties.Bounds.t
  val find_self_type : t -> Types.ty option
  val list_diagnostics : t -> Catalog.diagnostic list
  val list_applications : t -> (Syntax.id * Types.application) list
  val split_part : Syntax.expression -> (string * Syntax.name list * bool) option
  val elaborate_type : t -> Syntax.type_expression -> Types.ty
  val elaborate_mode : Syntax.mode option -> Language.Mode.t
  val elaborate_condition : t -> Syntax.condition -> Types.condition
  val add_condition : t -> Types.condition -> t
  val find_bounded_type : t -> Syntax.expression -> Types.ty option
  val elaborate_associated_expression : t -> Syntax.expression -> Types.ty option

  type bound_method = Elaborator.bound_method = {
    self_type : Types.ty;
    trait : Types.trait_reference;
    name : string;
    receiver : Path.receiver;
  }

  val list_bound_methods : t -> Types.ty -> string -> bound_method list
  val find_operand_method : bound_method list -> bound_method option

  type operand_callee = Elaborator.operand_callee =
    | Function_parameter of Syntax.name
    | Bound_method of { type_ : Syntax.expression; method_ : Syntax.name }
    | Not_a_callee

  type cost_operand = Elaborator.cost_operand = {
    written : Syntax.expression;
    cost_function : Syntax.name;
    metric : Language.Metric.t;
    callee : operand_callee;
  }

  val list_cost_operands : t -> Syntax.expression -> cost_operand list

  val elaborate_header :
    Lookups.t -> Resolve.Names.key -> (Environment.header, Catalog.diagnostic list) result

  val elaborate_definition : Lookups.t -> Resolve.Names.key -> Environment.elaborated_interface
end

module Constants = Constants
module Definition = Definition

module Properties : sig
  exception Recursion_limit of Catalog.Typing.t

  module Bounds : sig
    type t = Properties.Bounds.t

    val none : t
    val of_known : (Types.parameter * Types.trait_reference list) list -> t
    val close : Lookups.t -> (Types.parameter -> Types.trait_reference list) -> t
    val append : t -> t -> t
    val list : t -> Types.parameter -> Types.trait_reference list
  end

  val list_bound_closure :
    Lookups.t -> self:Types.ty -> Types.trait_reference -> Types.trait_reference list

  val list_known_bounds :
    Lookups.t -> list_bounds:Bounds.t -> Types.ty -> Types.trait_reference list

  val list_rigid_members :
    Lookups.t -> list_bounds:Bounds.t -> Types.ty -> Language.Builtin_type.t list

  type property = Properties.property = Copyable | Plain | View | Holds_function
  type decision = Properties.decision = Holds | Fails | Depends_on of Types.ty
  type occurrence = Environment.occurrence = In_place | Indirect | Function_input

  val compose_occurrences : occurrence -> occurrence -> occurrence

  type recursion = Properties.recursion = {
    recursive : Types.ty;
    occurrence : occurrence;
    defining : Path.t list;
  }

  val list_field_type_paths : package:Path.package -> Types.type_interface -> Path.t list

  val compute_component_facts :
    Lookups.t -> (Path.t * Types.type_interface) list -> (Path.t * Environment.type_facts) list
end

module Impls : module type of struct
  include Impls
end
with module Conformance := Impls.Conformance

module Grants = Grants
module Check = Check

type form_origin =
  | Written of Resolve.Names.key
  | Derived of Resolve.Names.key
  | Inherited of Resolve.Names.key

val find_form_origin :
  Lookups.t -> is_derived:(Path.t -> bool) -> Path.t -> (form_origin * Types.substitution) option
