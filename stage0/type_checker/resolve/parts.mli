type part = Header | Body | Member_header of int | Member_body of int

val reported :
  spans:Source.Definition_span.t array ->
  recovered:Source.Definition_span.t list ->
  Syntax.definition ->
  part ->
  Diagnostic.reported option

val recovery_report : Source.Definition_span.t -> Diagnostic.reported
