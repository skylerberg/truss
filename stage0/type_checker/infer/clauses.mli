val check_condition : State.state -> State.env -> Syntax.expression -> unit
val check_measures : State.state -> State.env -> Syntax.expression list -> unit
val check_cost : State.state -> State.env -> Syntax.cost -> unit
val check_time_terminates : State.state -> Syntax.clause -> uses:Types.capability_set -> unit

val check_under_condition :
  State.state -> id:Syntax.id -> Syntax.condition option -> (unit -> unit) -> unit

val build_under_condition :
  State.state ->
  id:Syntax.id ->
  Syntax.condition option ->
  (unit -> 'clause) ->
  'clause Core.conditional option
