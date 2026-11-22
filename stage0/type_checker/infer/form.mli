val build :
  Lookups.t ->
  signatures:Signatures.t ->
  resolved:Resolve.resolved ->
  tables:Tables.t ->
  context:Interface.Elaborator.t ->
  package:Path.package ->
  text:string Lazy.t ->
  key:Resolve.Names.key ->
  definition:Syntax.definition ->
  elaborated:Interface.Environment.elaborated_interface ->
  law_parameters:(string * Types.ty) list ->
  checks_body:bool ->
  has_syntax_error:(Resolve.Parts.part -> bool) ->
  Core.t

val list_capability_impls :
  Lookups.t ->
  list_bounds:Interface.Properties.Bounds.t ->
  package:Path.package ->
  Types.ty ->
  (Core.provided * Types.impl_interface) list

module For_testing : sig
  val is_written_expression : Syntax.expression -> Core.kind -> bool
end
