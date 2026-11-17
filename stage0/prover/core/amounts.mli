val run_code : State.context -> State.frame -> Mir.t -> type_:Types.ty -> State.frame * Logic.term
val make_empty_parts : State.context -> State.frame -> Types.ty -> Logic.term
val mentions_result : Mir.formula -> bool
val mentions_history : Mir.formula -> bool
val assume_typed : State.context -> State.frame -> Logic.term -> unit
val compare_lexicographically : Logic.term list -> Logic.term list -> Logic.term
val is_same_resource : Mir.cost -> locals:Logic.term Locals.t -> Costs.counter -> bool
val declare_bounded_amount : State.context -> State.frame -> Logic.term -> Logic.term

val declare_counted_amount :
  State.context ->
  State.frame ->
  location:State.location ->
  describe_upper_bound:(unit -> string) ->
  Costs.counter ->
  Costs.amount ->
  Logic.term

val compute_amount_within :
  State.context -> State.frame -> Costs.counter -> Logic.term -> Logic.term

val rely_on_lambda_costs : State.context -> Costs.counter -> Logic.term -> unit

val count_calls_in_one_call :
  State.context ->
  State.frame ->
  Costs.counter ->
  Costs.target ->
  Types.function_type ->
  Logic.term ->
  Costs.amount

val compute_callee_amount :
  ?method_cost:(Metric.t -> Logic.term) ->
  State.context ->
  State.frame ->
  location:State.location ->
  path:Path.t ->
  clauses:State.clauses list ->
  bind_frame:(State.clauses -> State.frame) ->
  uses:Types.capability list ->
  values:State.passed list ->
  change:(unit -> Logic.term) option ->
  Costs.counter ->
  Logic.term

val compute_step_amount :
  State.context ->
  State.frame ->
  location:State.location ->
  Invocation.t ->
  State.passed list ->
  Costs.counter ->
  Logic.term

val has_potential : State.context -> ?seen:Types.ty list -> Types.ty -> bool

val compute_potential :
  State.context -> State.frame -> ?seen:Types.ty list -> Types.ty -> Logic.term -> Logic.term

val compute_elements_potential : State.context -> Types.ty -> Logic.term -> Logic.term

val declare_method_cost :
  State.context ->
  State.frame ->
  Metric.t ->
  Path.t ->
  trait_arguments:Types.argument list ->
  Types.ty ->
  Logic.term

val compute_method_cost :
  State.context -> State.frame -> Metric.t -> Invocation.callee -> Logic.term
