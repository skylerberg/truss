type t = {
  lookups : Lookups.t;
  resolved : Resolve.resolved;
  bounds : (Types.parameter, Types.trait_reference list) Hashtbl.t;
  broken_parameters : (Types.parameter, Diagnostic.reported) Hashtbl.t;
  self_type : Types.ty option;
  self_trait : Types.trait_reference option;
  self_associated : (string * Types.ty) list;
  self_capabilities : (string * Types.capability_set) list;
  diagnostics : Diagnostic.in_definition list ref;
  named : (Syntax.id * Types.ty) list ref;
  spans : Source.Definition_span.t array;
}

val create :
  Lookups.t -> Resolve.resolved -> spans:Source.Definition_span.t array -> Environment.scope -> t

val record_diagnostic :
  Diagnostic.in_definition list ref ->
  ?fixes:Source.Definition_span.t Diagnostic.fix list ->
  Diagnostic.Code.types ->
  Source.Definition_span.t ->
  string ->
  Diagnostic.reported

val list_trait_closure : Lookups.t -> Path.t -> Path.t list
val show_path : Syntax.path -> string
val elaborate_type : t -> Syntax.type_expression -> Types.ty

val elaborate_header :
  Lookups.t -> Resolve.Names.key -> (Environment.header, Diagnostic.in_definition list) result

val elaborate_definition : Lookups.t -> Resolve.Names.key -> Environment.elaborated_interface
