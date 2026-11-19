val emit_debug_call :
  Memory_layout.env ->
  Emit_c.Ir_builder.t ->
  output:Lowered.operand ->
  Ground.ty ->
  Lowered.place ->
  unit

val build_debug : Memory_layout.env -> Ground.ty -> Emit_c.fragment
