val may_abort :
  State.context ->
  State.frame ->
  Callee.t ->
  Callee.definition ->
  State.contract ->
  State.passed list ->
  bool
