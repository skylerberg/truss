val encode_call :
  Memory_layout.env ->
  Emit_c.Builder.t ->
  output:Lowered.operand ->
  Ground.ty ->
  Lowered.place ->
  unit

val encode : Memory_layout.env -> Ground.ty -> Emit_c.fragment
val decode : Memory_layout.env -> Ground.ty -> string -> Lowered.static_value
val decode_booleans : string -> bool list
