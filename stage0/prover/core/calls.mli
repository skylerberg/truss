type applied = {
  frame : State.frame;
  result : Logic.term;
  end_lend : (State.frame -> Logic.term -> State.frame) option;
}

val call_contract :
  State.frame ->
  Invocation.site ->
  Callee.t ->
  Callee.definition ->
  State.contract ->
  State.passed list ->
  recursive_callee:Path.t option ->
  applied

val apply_call :
  State.frame ->
  Invocation.site ->
  Callee.t ->
  through:(Types.ty * Logic.term) option ->
  State.passed list ->
  (State.frame * Logic.term) option

val apply_lend :
  State.frame ->
  Invocation.site ->
  Callee.t ->
  through:(Types.ty * Logic.term) option ->
  State.passed list ->
  applied option
