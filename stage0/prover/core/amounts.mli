val declare_bounded_amount : State.context -> State.frame -> Logic.term -> Logic.term

val make_callback_cost :
  State.context -> State.frame -> Language.Metric.t -> Types.ty -> Logic.term -> Logic.term

val compute_construction_amount :
  State.context -> State.frame -> Types.ty -> string option -> Costs.counter -> Logic.term

val compute_method_cost :
  State.context -> State.frame -> Language.Metric.t -> Invocation.callee -> Logic.term

val spend_copy :
  ?literal:Language.Literal.t ->
  State.context ->
  State.frame ->
  declared:Types.ty ->
  Logic.term ->
  State.frame

val spend_wait_for_tasks : State.context -> State.frame -> State.frame

val spend_contract_call :
  State.context ->
  before:State.frame ->
  after:State.frame ->
  Invocation.site ->
  Invocation.t ->
  Path.t ->
  State.contract ->
  State.passed list ->
  changed:(int * Logic.term) list ->
  result:Logic.term ->
  result_type:Types.ty ->
  lent_final:(Logic.term -> Logic.term) option ->
  is_recursive:bool ->
  bind_frame:(State.clauses -> State.frame) ->
  State.frame

val spend_call_without_a_contract :
  State.context -> State.frame -> Invocation.t -> State.passed list -> State.frame

val spend_derived_equality :
  State.context ->
  State.frame ->
  Invocation.t ->
  State.passed list ->
  result_type:Types.ty ->
  result:Logic.term ->
  State.frame

val spend_indirect_call :
  State.context ->
  before:State.frame ->
  after:State.frame ->
  location:Obligation.location ->
  (Types.ty * Logic.term * Invocation.shape) option ->
  State.passed list ->
  result_type:Types.ty ->
  result:Logic.term ->
  State.frame

val spend_intrinsic :
  State.context ->
  State.frame ->
  Invocation.t ->
  Intrinsic.operation ->
  State.passed list ->
  changed:Logic.term list ->
  result_type:Types.ty ->
  result:Logic.term ->
  State.frame
