val note_lending : State.state -> Syntax.expression -> Types.result -> unit
val find_lent_mode : State.state -> Syntax.expression -> Types.mode option
val is_borrowed : State.state -> Syntax.expression -> bool
val classify_scrutinee_mode : State.state -> Syntax.expression -> Types.mode

type immutable = Read_only of string | Captured of string | Lent_read_only | Not_a_place
type mutation = Assignment | Passed_mut

val mutate : State.state -> State.env -> by:mutation -> Syntax.expression -> unit

type argument_form =
  | With_mode of Types.mode * Syntax.expression
  | Place
  | Lent of Types.mode
  | Temporary

val find_lent_field_mode : State.state -> Syntax.expression -> Types.ty -> Types.mode option

val check_mode :
  State.state -> State.env -> Syntax.expression -> Types.parameter_info -> Types.ty -> unit

val check_lent_value : State.state -> State.env -> Syntax.expression -> unit
val check_owned : State.state -> State.env -> Syntax.expression -> Types.ty -> unit
