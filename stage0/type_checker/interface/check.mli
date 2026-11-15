val bound_diagnostics :
  Lookups.t ->
  package:Path.package ->
  bounds:Impls.bounds ->
  (Syntax.span * Types.ty) list ->
  Syntax.diagnostic list

val diagnostics : Lookups.t -> Resolve.Names.key -> Syntax.diagnostic list
