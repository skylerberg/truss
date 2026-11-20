val select_arithmetic_method : Syntax.arithmetic -> Well_known.method_ * Well_known.associated
val infer_bitwise_result : State.state -> Source.Definition_span.t -> Types.ty -> Types.ty

val infer_shift_result :
  State.state ->
  left:Source.Definition_span.t * Types.ty ->
  right:Source.Definition_span.t * Types.ty ->
  Types.ty

val try_ : State.state -> State.env -> Syntax.expression -> Syntax.expression -> Types.ty

val check_prefix :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Syntax.prefix ->
  Syntax.expression ->
  Types.ty

val check_operator_call :
  State.state ->
  Syntax.id ->
  method_:Well_known.method_ ->
  output:Well_known.associated ->
  left:Syntax.expression * Types.ty ->
  right:(Syntax.expression * Types.ty) option ->
  Types.ty

val check_literal_operands : State.state -> left:Types.ty -> right:Types.ty -> unit

val check_binary :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Syntax.binary ->
  Syntax.expression ->
  Syntax.expression ->
  Types.ty

val check_any :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Syntax.expression ->
  Types.ty
