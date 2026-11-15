val ground_types : Ground.ty list

val debug_call :
  Memory_layout.env ->
  Emit_c.Builder.t ->
  output:Lowered.operand ->
  Ground.ty ->
  Lowered.place ->
  unit

val debug : Memory_layout.env -> Ground.ty -> Emit_c.Builder.instance
