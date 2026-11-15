val output_ty : Ground.ty
val output_parameter : Memory_layout.env -> Lowered.ty
val value_parameter : Ground.ty -> Lowered.ty
val signature : Memory_layout.env -> Lowered.ty list -> Lowered.signature

val call :
  Memory_layout.env ->
  Emit_c.Builder.t ->
  output:Lowered.operand ->
  Well_known.t ->
  Ground.ty ->
  Lowered.place ->
  unit

val call_with_bytes :
  Memory_layout.env ->
  Emit_c.Builder.t ->
  output:Lowered.operand ->
  Well_known.t ->
  elements:Lowered.operand ->
  length:Lowered.operand ->
  unit
