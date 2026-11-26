val enter_definition : State.context -> State.frame -> unit

val check_recursive_call :
  State.context ->
  State.frame ->
  Obligation.location ->
  path:Path.t ->
  State.clauses ->
  is_self_call:bool ->
  callee_entry:State.frame ->
  argument_at:(int -> Logic.term) ->
  unit

val find_induction_premise :
  State.context ->
  State.clauses ->
  is_self_call:bool ->
  callee_entry:State.frame ->
  argument_at:(int -> Logic.term) ->
  Logic.term option
