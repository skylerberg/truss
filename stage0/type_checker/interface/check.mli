val bound_diagnostics :
  Lookups.t ->
  package:Path.package ->
  bounds:Impls.bounds ->
  spans:Syntax.span array Lazy.t ->
  (Syntax.id * Types.ty) list ->
  Syntax.diagnostic list

val diagnostics : Lookups.t -> Resolve.Names.key -> Syntax.diagnostic list
