val check_block_value : State.state -> State.env -> ?expected:Types.ty -> Syntax.block -> Types.ty
val check_statement : State.state -> State.env -> Syntax.statement -> last:bool -> unit
val check_cost : State.state -> State.env -> Syntax.cost -> unit
