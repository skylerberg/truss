module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Elaborate = Interface.Elaborate

val expression : State.state -> State.env -> ?expected:Types.ty -> Syntax.expression -> Types.ty
val check : State.state -> State.env -> Syntax.expression -> Types.ty -> unit
