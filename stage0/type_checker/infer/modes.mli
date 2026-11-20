val note_lending : State.state -> Syntax.expression -> Types.result -> unit

type mutation = Assignment | Passed_mut

val mutate : State.state -> State.env -> by:mutation -> Syntax.expression -> unit
val find_lent_field_mode : State.state -> Syntax.expression -> Types.ty -> Language.Mode.t option

val check_mode :
  State.state ->
  State.env ->
  Syntax.expression ->
  Types.parameter_info ->
  Types.ty ->
  has_generic_type:bool ->
  unit

val note_place_without_keyword :
  State.state -> State.env -> Syntax.expression -> needs:Language.Mode.t -> unit

val note_owned_value : State.state -> State.env -> Syntax.expression -> unit
