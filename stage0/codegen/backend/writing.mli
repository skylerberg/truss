val output_ty : Ground.ty
val make_output_parameter : Memory_layout.env -> Lowered.ty
val make_value_parameter : Ground.ty -> Lowered.ty
val make_signature : Memory_layout.env -> Lowered.ty list -> Lowered.signature

val emit_write_call :
  Memory_layout.env ->
  Emit_c.Builder.t ->
  output:Lowered.operand ->
  Well_known.t ->
  Ground.ty ->
  Lowered.place ->
  unit

val emit_write_bytes_call :
  Memory_layout.env ->
  Emit_c.Builder.t ->
  output:Lowered.operand ->
  Well_known.t ->
  buffer:Lowered.operand ->
  length:Lowered.operand ->
  unit
