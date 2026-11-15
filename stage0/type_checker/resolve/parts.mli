type part = Header | Body | Member_header of int | Member_body of int

val broken : Syntax.definition -> part -> bool
val reported : Syntax.definition -> part -> Diagnostic.reported option
val recovery_report : Source.Definition_span.t -> Diagnostic.reported
