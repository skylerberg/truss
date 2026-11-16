module Environment = Environment
module Lookups = Lookups

module Elaborator : sig
  type t = Elaborator.t

  val create :
    Lookups.t -> Resolve.resolved -> spans:Source.Definition_span.t array -> Environment.scope -> t

  val read_span : t -> Syntax.id -> Source.Definition_span.t
  val list_bounds : t -> Types.parameter -> Types.trait_reference list
  val find_self_type : t -> Types.ty option
  val list_diagnostics : t -> Diagnostic.in_definition list
  val list_named_types : t -> (Syntax.id * Types.ty) list
  val show_path : Syntax.path -> string
  val elaborate_type : t -> Syntax.type_expression -> Types.ty

  val elaborate_header :
    Lookups.t -> Resolve.Names.key -> (Environment.header, Diagnostic.in_definition list) result

  val elaborate_definition : Lookups.t -> Resolve.Names.key -> Environment.elaborated_interface
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
    list_bounds:(Types.parameter -> Types.trait_reference list) ->
    Types.ty ->
    Types.trait_reference list

  type property = Properties.property = Copyable | Plain | View | Holds_function
  type answer = Properties.answer = Holds | Fails | Unknown of Types.ty
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
