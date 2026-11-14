(* Statements and terminators as C, written to a buffer, one line each. *)
val statement_c : C_types.context -> C_values.function_context -> Buffer.t -> Lir.statement -> unit

val terminator_c :
  C_types.context -> C_values.function_context -> Buffer.t -> Lir.terminator -> unit
