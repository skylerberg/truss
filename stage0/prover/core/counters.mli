exception Blocks_credited_potential of string list

val make_state : ?blocked_holders:string list -> unit -> State.cost_state
val lookup_spent : State.frame -> Costs.counter -> Logic.term
val read_condition : State.context -> Costs.counter -> Types.condition
val spend : State.context -> State.frame -> (Costs.counter -> Logic.term) -> State.frame
val declare_unknown_amount : State.context -> State.frame -> Costs.counter -> Logic.term
val make_potential_credit : State.context -> Logic.term -> Logic.term
val count_declared_potential : State.context -> of_:Types.ty -> Logic.term -> Logic.term
val count_whole_potential : State.context -> Logic.term -> Logic.term

val spend_operation :
  State.context ->
  State.frame ->
  potential_change:(unit -> Logic.term) option ->
  held:(unit -> Types.ty list) ->
  ?note:(Costs.counter -> Logic.term -> unit) ->
  (Costs.counter -> Costs.charge) ->
  State.frame

val spend_quantifier :
  State.context ->
  State.frame ->
  count:Logic.term ->
  mark:Query.mark ->
  bound:Logic.symbol ->
  before:State.frame ->
  after:State.frame ->
  State.frame

val enter_body :
  State.context ->
  State.frame ->
  (Costs.counter * Types.condition) list ->
  body:Mir.body option ->
  State.frame

val run_without_counters : State.context -> (unit -> 'a) -> 'a

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
  mark:Query.mark ->
  (Language.Metric.t * (Logic.term * Obligation.t list)) list

val has_another_cost :
  State.context ->
  Logic.term ->
  captures:Core.local list ->
  bounds:(Language.Metric.t * (Logic.term * Obligation.t list)) list ->
  bool

val note_lambda :
  State.context ->
  State.frame ->
  lambda_counters ->
  Logic.term ->
  captures:Core.local list ->
  bounds:(Language.Metric.t * (Logic.term * Obligation.t list)) list ->
  unit
