val bound_diagnostics :
  Lookups.t ->
  package:Path.package ->
  bounds:Impls.bounds ->
  spans:Source.Definition_span.t array ->
  (Syntax.id * Types.ty) list ->
  Diagnostic.in_definition list

val diagnostics : Lookups.t -> Resolve.Names.key -> Diagnostic.in_definition list
