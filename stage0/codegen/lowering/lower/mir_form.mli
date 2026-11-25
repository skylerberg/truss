val lower_mir_into :
  ?arguments:Lowered.place list -> Lowering.state -> Mir.Graph.t -> Lowered.place -> unit

val lower_code :
  Lowering.state ->
  Path.t ->
  parameters:Lowered.place list ->
  ?lending:Lowering.lending ->
  unit ->
  unit
