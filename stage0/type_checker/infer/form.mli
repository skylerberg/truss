val build :
  Lookups.t ->
  resolved:Resolve.resolved ->
  tables:Tables.t ->
  holes:Tables.t option ->
  context:Interface.Elaborator.t ->
  package:Path.package ->
  text:string Lazy.t ->
  key:Resolve.Names.key ->
  definition:Syntax.definition ->
  elaborated:Interface.Environment.elaborated_interface ->
  checks_body:bool ->
  Core.t

val list_capability_impls :
  Lookups.t ->
  list_bounds:(Types.parameter -> Types.trait_reference list) ->
  package:Path.package ->
  Types.ty ->
  (Core.provided * Types.impl_interface) list
