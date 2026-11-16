val select_arithmetic_trait : Syntax.arithmetic -> Path.t * string
val infer_bitwise_result : State.state -> Source.Definition_span.t -> Types.ty -> Types.ty

val infer_shift_result :
  State.state ->
  left:Source.Definition_span.t * Types.ty ->
  right:Source.Definition_span.t * Types.ty ->
  Types.ty

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
  operands:Tables.argument list ->
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
