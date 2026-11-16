type context = {
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

val create :
  Lookups.t ->
  Resolve.resolved ->
  spans:Source.Definition_span.t array ->
  Environment.scope ->
  context

val show_path : Syntax.path -> string
val scope : context -> Environment.scope
val report : context -> Diagnostic.Code.types -> Source.Definition_span.t -> string -> unit
val error : context -> Diagnostic.Code.types -> Source.Definition_span.t -> string -> Types.ty
val bug : ('a, unit, string, 'b) format4 -> 'a
val target : context -> Syntax.name -> Resolve.target option
val type_ : context -> Syntax.type_expression -> Types.ty

val trait_reference :
  ?capability:bool ->
  context ->
  Syntax.path_type ->
  (Types.trait_reference, Diagnostic.reported) result

val trait_bounds : context -> Syntax.path_type list -> Types.trait_reference list
val capabilities : context -> Syntax.capability_reference list -> Types.capability_set
val generics : context -> Path.t -> Syntax.generic_parameter list -> Types.generic list
val terminates : Syntax.clause list -> bool

val signature :
  context ->
  owner:Path.t ->
  head:Types.generic list ->
  self_type:Types.ty option ->
  Syntax.signature ->
  Types.signature
