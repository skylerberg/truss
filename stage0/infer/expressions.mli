module T = Types
module C = Tables
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower

val expression :
  State.state -> State.env -> ?expected:State.T.ty -> Syntax.expression -> Values.T.ty

val check : State.state -> State.env -> Syntax.expression -> Values.T.ty -> unit
