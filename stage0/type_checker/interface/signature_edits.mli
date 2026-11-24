val find_clause_insertion :
  Resolve.Names.lookups ->
  Resolve.Names.key ->
  string ->
  Source.Definition_span.t Diagnostic.edit option

val find_capability_insertion :
  Resolve.Names.lookups ->
  Resolve.Names.key ->
  string ->
  Source.Definition_span.t Diagnostic.edit option
