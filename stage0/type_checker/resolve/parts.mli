type part = Header | Body | Member_header of int | Member_body of int

val list_broken_parts :
  spans:Source.Definition_span.t array ->
  syntax_errors:Source.Definition_span.t list ->
  Syntax.definition ->
  part list
