val list_application_diagnostics :
  Lookups.t ->
  package:Path.package ->
  list_bounds:Impls.bounds ->
  (Syntax.id * Types.application) list ->
  Catalog.diagnostic list

val list_diagnostics : Lookups.t -> Resolve.Names.key -> Catalog.diagnostic list
