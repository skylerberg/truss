val bound_diagnostics :
  Query.context ->
  package:Path.package ->
  bounds:Impls.bounds ->
  (Syntax.span * Types.ty) list ->
  Syntax.diagnostic list

val diagnostics : (Resolve.Names.key, Syntax.diagnostic list) Query.query
val reported : Query.context -> Path.t -> Diagnostic.reported option
