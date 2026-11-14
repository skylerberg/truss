(* Statements and terminators as C, written to a buffer, one line each. *)
val statement_c :
  C_types.context -> C_values.function_context -> Buffer.t -> Lowered.statement -> unit

(* A terminator, with [label] giving the C label of each block it goes to. *)
val terminator_c :
  C_types.context ->
  C_values.function_context ->
  label:(Lowered.block -> string) ->
  Buffer.t ->
  Lowered.terminator ->
  unit
