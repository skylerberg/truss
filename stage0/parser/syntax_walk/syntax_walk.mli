val visit_expression_parts :
  on_expression:(Syntax.expression -> unit) ->
  on_statement:(Syntax.statement -> unit) ->
  Syntax.expression ->
  unit

val visit_statement_parts :
  on_expression:(Syntax.expression -> unit) ->
  on_statement:(Syntax.statement -> unit) ->
  Syntax.statement ->
  unit

val contains_break : Syntax.block -> bool
val visit_children : (Syntax.expression -> unit) -> Syntax.expression -> unit
val visit_statement : (Syntax.expression -> unit) -> Syntax.statement -> unit
val visit_type_expression : (Syntax.expression -> unit) -> Syntax.type_expression -> unit
val visit_clause : (Syntax.expression -> unit) -> Syntax.clause -> unit
val visit_loop_clause : (Syntax.expression -> unit) -> Syntax.loop_clause -> unit
val visit_generic_parameter : (Syntax.expression -> unit) -> Syntax.generic_parameter -> unit
val visit_definition_name : (Syntax.expression -> unit) -> Syntax.definition_name -> unit
val visit_signature : (Syntax.expression -> unit) -> Syntax.signature -> unit

val visit_definition :
  ?on_statement:(Syntax.statement -> unit) ->
  (Syntax.expression -> unit) ->
  Syntax.definition ->
  unit

val collect_names : Source.Definition_span.t array -> Syntax.definition -> Syntax.name list
val is_literal_bound : Syntax.bound -> bool
val is_callback_contract_clause : Syntax.clause -> bool
val can_mention_inputs : Syntax.clause -> bool
val has_callback_contract : Syntax.function_type -> bool
