type call_amount = {
  call : Catalog.Prover.quoted;
  callee : Path.t;
  states_cost : bool;
  counts_potential : bool;
  counter : Costs.counter;
  amount : Logic.term;
}

val list_call_amounts : Query.t -> call_amount list
val declare_bounded_amount : State.frame -> Logic.term -> Logic.term
val make_callback_cost : State.frame -> Language.Metric.t -> Types.ty -> Logic.term -> Logic.term

val compute_construction_amount :
  State.environment -> Types.ty -> string option -> Costs.counter -> Logic.term

val compute_method_cost : State.frame -> Language.Metric.t -> Callee.t -> Logic.term

val spend_copy :
  ?literal:Language.Literal.t -> State.frame -> declared:Types.ty -> Logic.term -> State.frame

val spend_wait_for_tasks : State.frame -> State.frame

val spend_contract_call :
  before:State.frame ->
  after:State.frame ->
  Invocation.site ->
  Callee.t ->
  Callee.definition ->
  State.contract ->
  State.passed list ->
  changed:(int * Logic.term) list ->
  result:Logic.term ->
  result_type:Types.ty ->
  final:Logic.term option ->
  is_recursive:bool ->
  bind_frame:(State.clauses -> State.frame) ->
  read_requires:(State.clauses -> Logic.term) ->
  State.frame

val spend_call_without_a_contract : State.frame -> Callee.t -> State.passed list -> State.frame

val spend_derived_equality :
  State.frame ->
  Callee.t ->
  State.passed list ->
  result_type:Types.ty ->
  result:Logic.term ->
  State.frame

val spend_indirect_call :
  before:State.frame ->
  after:State.frame ->
  location:Obligation.location ->
  Types.function_type ->
  Logic.term ->
  State.passed list ->
  changed:(int * Logic.term) list ->
  result_type:Types.ty ->
  result:Logic.term ->
  State.frame

val spend_intrinsic :
  State.frame ->
  Callee.t ->
  Intrinsic.operation ->
  State.passed list ->
  changed:Logic.term list ->
  result_type:Types.ty ->
  result:Logic.term ->
  State.frame
