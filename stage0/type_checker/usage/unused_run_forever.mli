val find :
  Lookups.t ->
  Resolve.Names.key ->
  Syntax.definition ->
  Resolve.resolved ->
  Catalog.diagnostic option
