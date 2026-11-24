val read_expected_head : State.state -> Types.ty -> Types.ty
val read_actual_head : State.state -> Syntax.expression -> Types.ty -> Types.ty
val read_checked_head : State.state -> State.env -> Syntax.expression -> Types.ty

val convert :
  State.state ->
  State.env ->
  ?argument:Language.Mode.t ->
  ?expression:Syntax.expression ->
  Source.Definition_span.t ->
  actual:Types.ty ->
  expected:Types.ty ->
  unit

val coerce :
  State.state ->
  State.env ->
  ?argument:Language.Mode.t ->
  Syntax.expression ->
  actual:Types.ty ->
  expected:Types.ty ->
  unit
