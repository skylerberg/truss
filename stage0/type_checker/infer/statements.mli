val record_integer_range :
  State.state ->
  loop:Syntax.id ->
  owner:Catalog.Inference.range_owner ->
  admits_integer:bool ->
  Syntax.expression ->
  Types.ty ->
  inclusive:bool ->
  unit

val statement_diverges : State.state -> Syntax.statement -> bool
val check_block_value : State.state -> State.env -> ?expected:Types.ty -> Syntax.block -> Types.ty
val check_statement : State.state -> State.env -> Syntax.statement -> last:bool -> unit

val find_elements_loop :
  State.state ->
  cause:State.cause ->
  at:Core.origin ->
  Types.ty ->
  Language.Mode.t ->
  (Tables.loop * Types.ty * Language.Mode.t) option
