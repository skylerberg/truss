type promise = {
  counter : Costs.counter;
  clause : Mir.cost;
  written_in : State.source;
  inherited : bool;
}

val list_promises :
  State.context ->
  State.source ->
  Logic.term Locals.t ->
  Mir.cost list ->
  inherited:bool ->
  counts_provider_potential:bool ->
  promise list

val enter_definition :
  State.context -> State.frame -> promise list -> body:Mir.body option -> State.frame

val check_promise_amounts :
  State.context -> State.frame -> promise list -> output:Types.ty option -> unit

val check_promise :
  ?restated:Types.ty * string * Types.trait_reference * Types.trait_reference ->
  ?cited:Resolve.Names.key * Core.origin ->
  State.context ->
  State.frame ->
  promise ->
  at:State.frame ->
  location:Obligation.location ->
  unit
