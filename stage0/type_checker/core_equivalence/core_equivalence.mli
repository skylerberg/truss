type parameters = Core.parameter list * Core.parameter list

val equal_condition : parameters:parameters -> Core.condition -> Core.condition -> bool
val equal_expression : parameters:parameters -> Core.expression -> Core.expression -> bool
val equal_cost : parameters:parameters -> Core.cost -> Core.cost -> bool
val equal_law : Core.law -> Core.law -> bool
