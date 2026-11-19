val check_binding_pattern :
  State.state -> State.env -> Syntax.pattern -> Types.ty -> is_var:bool -> mode:Types.mode -> unit

val check_pattern :
  State.state -> State.env -> Syntax.pattern -> Types.ty -> mode:Types.mode -> unit

val check_parameter_pattern :
  State.state -> State.env -> Syntax.pattern -> Types.ty -> mode:Types.mode -> unit

val check_literal_fits : State.state -> Syntax.expression -> Z.t -> Types.ty -> unit
val find_character_tag : State.state -> Syntax.string_literal -> Intrinsic.builtin option

val check_character_literal :
  State.state -> Syntax.id -> Syntax.string_literal -> Intrinsic.builtin -> Types.ty
