val call_tasks_bool : Lowering.state -> Well_known.method_ -> Lowered.place list -> Lowered.operand
val with_group : Lowering.state -> (Lowered.place -> unit) -> unit
val compute_task_function_type : Lowering.state -> Lowered.ty

val lower_task_body :
  Lowering.state ->
  id:Mir.task ->
  group:Lowered.place ->
  parts:Lowered.local list ->
  (Lowering.task -> unit) ->
  Lowered.rvalue

val lock_evidence :
  Lowering.state ->
  tasks:Lowered.operand ->
  (Path.t * Lowered.operand) list ->
  (Path.t * Lowered.operand) list

val cancel :
  Lowering.state ->
  task:Mir.task ->
  winner:Mir.local ->
  number:int ->
  value:(Lowered.place * Ground.ty * Mir.local) option ->
  unit

val spawn_iteration :
  Lowering.state -> Lowering.spawn_loop -> on_not_spawned:(unit -> unit) -> (unit -> unit) -> unit

val spawn_with_item :
  Lowering.state ->
  Lowering.spawn_loop ->
  Lowered.place ->
  owned:bool ->
  each:(Lowered.place -> unit) ->
  unit
