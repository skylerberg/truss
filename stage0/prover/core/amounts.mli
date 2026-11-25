val declare_bounded_amount : State.context -> State.frame -> Logic.term -> Logic.term

val compute_callee_amount :
  ?method_cost:(Language.Metric.t -> Logic.term) ->
  State.context ->
  State.frame ->
  is_recursive:bool ->
  clauses:State.clauses list ->
  bind_frame:(State.clauses -> State.frame) ->
  uses:Types.capability_set ->
  values:State.passed list ->
  counts_provider_potential:bool ->
  Costs.counter ->
  Costs.charge

val compute_step_amount :
  ?result:Logic.term ->
  State.context ->
  State.frame ->
  Invocation.t ->
  State.passed list ->
  Costs.counter ->
  Costs.charge

val make_callback_cost :
  State.context -> State.frame -> Language.Metric.t -> Types.ty -> Logic.term -> Logic.term

val compute_function_value_amount :
  State.context ->
  State.frame ->
  location:Obligation.location ->
  Types.function_type ->
  Logic.term ->
  values:State.passed list ->
  Costs.counter ->
  Costs.charge

val compute_construction_amount :
  State.context -> State.frame -> Types.ty -> string option -> Costs.counter -> Logic.term

val compute_method_cost :
  State.context -> State.frame -> Language.Metric.t -> Invocation.callee -> Logic.term

val has_method_cost : State.context -> Invocation.callee -> Path.t -> bool

val spend_copy :
  ?literal:Language.Literal.t ->
  State.context ->
  State.frame ->
  declared:Types.ty ->
  Logic.term ->
  State.frame

val spend_wait_for_tasks : State.context -> State.frame -> State.frame
