module Environment = Environment
module Lookups = Lookups

module Elaborate : sig
  type context = Elaborate.context = {
    lookups : Lookups.t;
    resolved : Resolve.resolved;
    bounds : (Types.parameter, Types.trait_reference list) Hashtbl.t;
    self_type : Types.ty option;
    self_trait : Types.trait_reference option;
    self_associated : (string * Types.ty) list;
    self_capabilities : (string * Types.capability_set) list;
    diagnostics : Diagnostic.in_definition list ref;
    named : (Syntax.id * Types.ty) list ref;
    spans : Source.Definition_span.t array;
  }

  val create_context :
    Lookups.t ->
    Resolve.resolved ->
    spans:Source.Definition_span.t array ->
    Environment.scope ->
    context

  val show_path : Syntax.path -> string
  val type_ : context -> Syntax.type_expression -> Types.ty

  val header :
    Lookups.t -> Resolve.Names.key -> (Environment.header, Diagnostic.in_definition list) result

  val definition : Lookups.t -> Resolve.Names.key -> Environment.elaborated_interface
end

module Constants = Constants
module Definition = Definition

module Properties : sig
  exception Recursion_limit of string

  val make_trait_substitution :
    Types.trait_interface -> self:Types.ty -> Types.trait_reference -> Types.substitution

  val list_bound_closure :
    Lookups.t -> self:Types.ty -> Types.trait_reference -> Types.trait_reference list

  val list_known_bounds :
    Lookups.t ->
    bounds:(Types.parameter -> Types.trait_reference list) ->
    Types.ty ->
    Types.trait_reference list

  type occurrence = Environment.occurrence = In_place | Indirect | Function_input

  val compose_occurrences : occurrence -> occurrence -> occurrence

  type recursion = Properties.recursion = {
    recursive : Types.ty;
    occurrence : occurrence;
    defining : Path.t list;
  }

  type contents = Properties.contents = {
    contained : (Types.ty * occurrence) list;
    recursions : recursion list;
  }

  val list_field_type_paths : package:Path.package -> Types.type_interface -> Path.t list

  val compute_component_facts :
    Lookups.t -> (Path.t * Types.type_interface) list -> (Path.t * Environment.type_facts) list
end

module Impls = Impls
module Grants = Grants
module Check = Check
