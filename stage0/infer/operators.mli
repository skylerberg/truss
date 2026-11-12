module T = Types
module C = Tables
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower

val try_ : State.state -> State.env -> Syntax.expression -> Syntax.expression -> Pattern_typing.T.ty

val with_ :
  State.state ->
  State.env ->
  Syntax.expression ->
  Syntax.expression ->
  Syntax.update list ->
  Types.ty

val prefix :
  State.state ->
  State.env ->
  ?expected:State.T.ty ->
  Syntax.expression ->
  Syntax.prefix ->
  Syntax.expression ->
  Pattern_typing.T.ty

val operator_call :
  ?operands:State.C.argument list ->
  State.state ->
  Syntax.expression ->
  trait:Path.t ->
  method_:string ->
  left:State.T.ty ->
  right:Pattern_typing.T.ty option ->
  Pattern_typing.T.ty

val literal_operands : State.state -> left:Unify.T.ty -> right:Unify.T.ty -> unit

val binary :
  State.state ->
  State.env ->
  ?expected:State.T.ty ->
  Syntax.expression ->
  Syntax.binary ->
  Syntax.expression ->
  Syntax.expression ->
  Pattern_typing.T.ty

val any_ :
  State.state ->
  State.env ->
  ?expected:Unify.T.ty ->
  Syntax.expression ->
  Syntax.expression ->
  Pattern_typing.T.ty
