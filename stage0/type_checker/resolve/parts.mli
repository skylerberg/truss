type part = Header | Body | Member_header of int | Member_body of int

val find_recovered_report :
  spans:Source.Definition_span.t array ->
  recovered:Source.Definition_span.t list ->
  Syntax.definition ->
  part ->
  Diagnostic.reported option
