type site = Value | Default | Evaluated_condition

val check : State.state -> site -> Syntax.expression -> unit
val check_type : State.state -> Syntax.type_expression -> Types.ty -> unit
