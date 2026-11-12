module T = Types

val expression_hook :
  (State.state -> State.env -> ?expected:State.T.ty -> Syntax.expression -> State.T.ty) ref

val check_hook : (State.state -> State.env -> Syntax.expression -> State.T.ty -> unit) ref
val expression : State.state -> State.env -> ?expected:State.T.ty -> Syntax.expression -> State.T.ty
val check : State.state -> State.env -> Syntax.expression -> State.T.ty -> unit
