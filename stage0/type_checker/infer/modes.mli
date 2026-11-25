type mutation = Catalog.Inference.mutation = Assignment | Passed_mut

val mutate : State.state -> State.env -> by:mutation -> Syntax.expression -> unit
val is_mutable : State.state -> State.env -> Syntax.expression -> bool
val find_lent_field_mode : State.state -> Syntax.expression -> Types.ty -> Language.Mode.t option

val check_mode :
  State.state -> State.env -> Syntax.expression -> Types.parameter_info -> Types.ty -> unit

val note_place_without_keyword :
  State.state -> State.env -> Syntax.expression -> needs:Language.Mode.t -> unit

val infer_view_of_borrowed_place :
  State.state -> State.env -> Syntax.expression -> actual:Types.ty -> expected:Types.ty -> unit

val note_owned_value : State.state -> State.env -> Syntax.expression -> unit
