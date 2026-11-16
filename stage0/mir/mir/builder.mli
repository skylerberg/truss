val of_definition : ?is_specification:bool -> Core.definition -> Tree.t option
val of_expression : ?parameters:Core.parameter list -> Core.expression -> Tree.t

val of_clause :
  ?is_executable:bool -> parameters:Core.parameter list -> Core.expression -> Tree.formula

val of_specification : entry_locals:Core.local list -> Core.expression -> Tree.formula
val of_law_statement : entry_locals:Core.local list -> Core.block -> Tree.formula
val names_of : Core.expression -> (Core.local * Core.origin) list
