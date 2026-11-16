val write_statement :
  C_types.context -> C_values.function_context -> Buffer.t -> Lowered.statement -> unit

val write_terminator :
  C_types.context -> C_values.function_context -> Buffer.t -> Lowered.terminator -> unit
