val write_statement :
  Emission.t -> C_values.function_context -> Buffer.t -> Lowered.statement -> unit

val write_terminator :
  Emission.t -> C_values.function_context -> Buffer.t -> Lowered.terminator -> unit
