val note_lending : State.state -> Syntax.expression -> Types.result -> unit
val find_lent_mode : State.state -> Syntax.expression -> Language.Mode.t option
val is_borrowed : State.state -> Syntax.expression -> bool
val classify_scrutinee_mode : State.state -> Syntax.expression -> Language.Mode.t

type mutation = Assignment | Passed_mut

val mutate : State.state -> State.env -> by:mutation -> Syntax.expression -> unit
val find_lent_field_mode : State.state -> Syntax.expression -> Types.ty -> Language.Mode.t option

val check_mode :
  State.state -> State.env -> Syntax.expression -> Types.parameter_info -> Types.ty -> unit

val note_place_without_keyword :
  State.state -> State.env -> Syntax.expression -> needs:Language.Mode.t -> unit

val note_owned_value : State.state -> State.env -> Syntax.expression -> unit
