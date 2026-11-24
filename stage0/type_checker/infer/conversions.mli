val read_expected_head : State.state -> Types.ty -> Types.ty
val read_actual_head : State.state -> Syntax.expression -> Types.ty -> Types.ty
val read_checked_head : State.state -> State.env -> Syntax.expression -> Types.ty
val find_view_as : owned:Types.ty -> view:Types.ty -> Types.ty option

val convert :
  State.state ->
  State.env ->
  ?argument:Language.Mode.t ->
  ?takes_view_as_owner:bool ->
  ?expression:Syntax.expression ->
  Core.origin ->
  actual:Types.ty ->
  expected:Types.ty ->
  unit

val coerce :
  State.state ->
  State.env ->
  ?argument:Language.Mode.t ->
  ?takes_view_as_owner:bool ->
  Syntax.expression ->
  actual:Types.ty ->
  expected:Types.ty ->
  unit
