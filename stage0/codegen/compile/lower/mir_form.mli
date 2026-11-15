val mir_of : Definitions.context -> Path.t -> Mir.Graph.t
val parameter_defaults : Definitions.context -> Path.t -> (int * Mir.Graph.t) list
val parameter_of : Mir.Graph.body -> Mir.local -> Types.mode * string * Types.ty

val mir_into :
  ?arguments:Lowered.place list -> Lowering.state -> Mir.Graph.t -> Lowered.place -> unit

val fill_defaults :
  Lowering.state ->
  Lowered.place ->
  Mir.Graph.body ->
  defaults:(int * Mir.Graph.t) list ->
  Lowered.place list ->
  Lowered.place list

val lower_code :
  Lowering.state ->
  Path.t ->
  parameters:Lowered.place list ->
  ?lending:Lowering.lending ->
  unit ->
  unit
