val expression_parts :
  expression:(Syntax.expression -> unit) ->
  statement:(Syntax.statement -> unit) ->
  Syntax.expression ->
  unit

val statement_parts :
  expression:(Syntax.expression -> unit) ->
  statement:(Syntax.statement -> unit) ->
  Syntax.statement ->
  unit

val contains_break : Syntax.block -> bool
val children : (Syntax.expression -> unit) -> Syntax.expression -> unit
val statement : (Syntax.expression -> unit) -> Syntax.statement -> unit
val type_expression : (Syntax.expression -> unit) -> Syntax.type_expression -> unit
val clause : (Syntax.expression -> unit) -> Syntax.clause -> unit
val loop_clause : (Syntax.expression -> unit) -> Syntax.loop_clause -> unit
val generic_parameter : (Syntax.expression -> unit) -> Syntax.generic_parameter -> unit
val definition_name : (Syntax.expression -> unit) -> Syntax.definition_name -> unit
val signature : (Syntax.expression -> unit) -> Syntax.signature -> unit

val definition :
  ?statement:(Syntax.statement -> unit) -> (Syntax.expression -> unit) -> Syntax.definition -> unit

val spans : Syntax.definition -> Source.Definition_span.t array
val names : Syntax.definition -> Syntax.name list
val without_positions : Syntax.definition -> Syntax.definition
