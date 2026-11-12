module T = Types
module C = Tables
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower

val block_value : State.state -> State.env -> ?expected:State.T.ty -> Syntax.block -> Operators.T.ty
val statement : State.state -> State.env -> Syntax.statement -> last:bool -> unit
