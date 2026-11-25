type part = Header | Body | Member_header of int | Member_body of int

val find_syntax_error :
  spans:Source.Definition_span.t array ->
  syntax_errors:Source.Definition_span.t list ->
  Syntax.definition ->
  part ->
  Catalog.reported option
