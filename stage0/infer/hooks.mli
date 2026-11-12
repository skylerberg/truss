val expression_hook :
  (State.state -> State.env -> ?expected:Types.ty -> Syntax.expression -> Types.ty) ref

val check_hook : (State.state -> State.env -> Syntax.expression -> Types.ty -> unit) ref
val expression : State.state -> State.env -> ?expected:Types.ty -> Syntax.expression -> Types.ty
val check : State.state -> State.env -> Syntax.expression -> Types.ty -> unit
