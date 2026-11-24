val list_bound_diagnostics :
  Lookups.t ->
  package:Path.package ->
  list_bounds:Impls.bounds ->
  (Syntax.id * Types.ty) list ->
  Catalog.description list

val list_diagnostics : Lookups.t -> Resolve.Names.key -> Catalog.description list
