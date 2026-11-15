val statement_c :
  C_types.context -> C_values.function_context -> Buffer.t -> Lowered.statement -> unit

val terminator_c :
  C_types.context -> C_values.function_context -> Buffer.t -> Lowered.terminator -> unit
