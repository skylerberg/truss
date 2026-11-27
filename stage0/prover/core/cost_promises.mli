val find_call_target : Query.t -> Logic.term -> Core.local option
val is_bounded : Query.t -> Costs.counter -> bool

type promise = {
  counter : Costs.counter;
  clause : Mir.cost;
  written_in : State.source;
  inherited : bool;
}

val list_promises :
  State.environment ->
  Query.t ->
  State.source ->
  Logic.term Locals.t ->
  Mir.cost list ->
  inherited:bool ->
  counts_provider_potential:bool ->
  promise list

val enter_definition : State.frame -> promise list -> body:Mir.body option -> State.frame
val check_promise_amounts : State.frame -> promise list -> output:Types.ty option -> unit

val check_promise :
  ?cited:Resolve.Names.key * Core.origin ->
  State.frame ->
  promise ->
  at:State.frame ->
  location:Obligation.location ->
  unit
