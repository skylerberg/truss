val make_state :
  ?loops_counting_potential:(Core.origin * Costs.counter) list -> unit -> State.cost_state

val lookup_spent : State.frame -> Costs.counter -> Logic.term
val read_condition : State.context -> Costs.counter -> Types.condition
val spend : State.context -> State.frame -> (Costs.counter -> Logic.term) -> State.frame
val declare_unknown_amount : State.context -> State.frame -> Costs.counter -> Logic.term
val charge_potential : State.context -> Costs.counter -> Logic.term Lazy.t -> Logic.term

val spend_operation :
  State.context ->
  State.frame ->
  potential_change:(unit -> Logic.term) option ->
  ?note:(Costs.counter -> Logic.term -> unit) ->
  (Costs.counter -> Costs.charge) ->
  State.frame

val spend_quantifier :
  State.context ->
  State.frame ->
  count:Logic.term ->
  fresh_mark:int ->
  bound:Logic.symbol ->
  before:State.frame ->
  after:State.frame ->
  State.frame

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
  State.context ->
  State.frame ->
  promise ->
  at:State.frame ->
  location:Obligation.location ->
  compute_potential_at_entry:(unit -> Logic.term) ->
  unit

type lambda_counters

val enter_lambda :
  State.context -> State.frame -> Types.function_type -> Mir.body -> lambda_counters * State.frame

val leave_lambda : State.context -> lambda_counters -> unit

val check_lambda_exits :
  State.context ->
  lambda_counters ->
  State.frame list ->
  Obligation.location ->
  type_:Types.ty ->
  fresh_mark:int ->
  facts_mark:int ->
  (Language.Metric.t * (Logic.term * Obligation.t list)) list

val note_lambda :
  State.context ->
  lambda_counters ->
  Logic.term ->
  captures:Core.local list ->
  bounds:(Language.Metric.t * (Logic.term * Obligation.t list)) list ->
  unit
