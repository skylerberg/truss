module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower

val try_ : State.state -> State.env -> Syntax.expression -> Syntax.expression -> Types.ty

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
  ?expected:Types.ty ->
  Syntax.expression ->
  Syntax.prefix ->
  Syntax.expression ->
  Types.ty

val operator_call :
  ?operands:Tables.argument list ->
  State.state ->
  Syntax.expression ->
  trait:Path.t ->
  method_:string ->
  left:Types.ty ->
  right:Types.ty option ->
  Types.ty

val literal_operands : State.state -> left:Types.ty -> right:Types.ty -> unit

val binary :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Syntax.binary ->
  Syntax.expression ->
  Syntax.expression ->
  Types.ty

val any_ :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Syntax.expression ->
  Types.ty
