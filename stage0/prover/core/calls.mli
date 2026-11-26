type applied = {
  frame : State.frame;
  result : Logic.term;
  end_lend : (State.frame -> Logic.term -> State.frame) option;
}

val call_contract :
  State.context ->
  State.frame ->
  Invocation.site ->
  Callee.t ->
  Callee.definition ->
  State.contract ->
  State.passed list ->
  recursive_callee:Path.t option ->
  applied

val apply_call :
  State.context ->
  State.frame ->
  Invocation.site ->
  Callee.t ->
  through:(Types.ty * Logic.term * Invocation.shape) option ->
  State.passed list ->
  (State.frame * Logic.term) option

val apply_lend :
  State.context ->
  State.frame ->
  Invocation.site ->
  Callee.t ->
  through:(Types.ty * Logic.term * Invocation.shape) option ->
  State.passed list ->
  applied option
