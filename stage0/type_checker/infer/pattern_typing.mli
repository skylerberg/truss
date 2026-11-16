val binding_pattern :
  State.state -> State.env -> Syntax.pattern -> Types.ty -> is_var:bool -> mode:Types.mode -> unit

val pattern : State.state -> State.env -> Syntax.pattern -> Types.ty -> mode:Types.mode -> unit
val check_literal_fits : State.state -> Syntax.expression -> Z.t -> Types.ty -> unit
val character_tag : State.state -> Syntax.string_literal -> Intrinsic.builtin option

val character_literal :
  State.state -> Syntax.id -> Syntax.string_literal -> Intrinsic.builtin -> Types.ty
