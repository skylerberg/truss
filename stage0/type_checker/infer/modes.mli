val note_lending : State.state -> Syntax.expression -> Types.result -> unit
val find_lent_mode : State.state -> Syntax.expression -> Types.mode option
val is_borrowed : State.state -> Syntax.expression -> bool
val classify_scrutinee_mode : State.state -> Syntax.expression -> Types.mode

type mutation = Assignment | Passed_mut

val mutate : State.state -> State.env -> by:mutation -> Syntax.expression -> unit
val find_lent_field_mode : State.state -> Syntax.expression -> Types.ty -> Types.mode option

val check_mode :
  State.state -> State.env -> Syntax.expression -> Types.parameter_info -> Types.ty -> unit

val check_lent_value : State.state -> State.env -> Syntax.expression -> unit
val note_place_without_own : State.state -> State.env -> Syntax.expression -> unit
val note_owned_value : State.state -> State.env -> Syntax.expression -> unit
