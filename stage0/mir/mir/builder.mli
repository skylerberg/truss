val of_definition : is_specification:bool -> origin:Core.origin -> Core.definition -> Tree.t option
val of_expression : Core.expression -> Tree.t
val of_default : Core.expression -> Tree.t

val of_clause :
  ?is_executable:bool -> parameters:Core.parameter list -> Core.expression -> Tree.formula

val of_specification : entry_locals:Core.local list -> Core.expression -> Tree.formula

val of_law_statement :
  entry_locals:Core.local list -> origin:Core.origin -> Core.block -> Tree.formula

val list_names : Core.expression -> (Core.local * Core.origin) list
