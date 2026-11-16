val check_call :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Syntax.expression ->
  Syntax.argument list ->
  Types.ty
