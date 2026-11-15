open Tree

val of_definition : ?is_specification:bool -> Core.definition -> t option
val of_expression : ?parameters:Core.parameter list -> Core.expression -> t
val of_clause : ?is_executable:bool -> parameters:Core.parameter list -> Core.expression -> formula
val of_specification : entry_locals:Core.local list -> Core.expression -> formula
val of_law_statement : entry_locals:Core.local list -> Core.block -> formula
val names_of : Core.expression -> (Core.local * Core.origin) list
