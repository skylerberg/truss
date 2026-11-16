val block_value : State.state -> State.env -> ?expected:Types.ty -> Syntax.block -> Types.ty
val statement : State.state -> State.env -> Syntax.statement -> last:bool -> unit
