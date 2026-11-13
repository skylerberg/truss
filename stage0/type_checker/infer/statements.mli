module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower

val block_value : State.state -> State.env -> ?expected:Types.ty -> Syntax.block -> Types.ty
val statement : State.state -> State.env -> Syntax.statement -> last:bool -> unit
