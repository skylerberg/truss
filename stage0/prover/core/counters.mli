exception Blocks_credited_potential of string list

type lambda_bound = Logic.term * Obligation.t list

val list_counters : Query.t -> Costs.counter list
val run_counting : Query.t -> Costs.counter list -> (unit -> 'a) -> 'a
val count_recursive_costs_assumed : Query.t -> int
val note_recursive_cost_assumed : Query.t -> unit
val find_lambda_captures : Query.t -> Logic.term -> Core.local list option
val assumes_recursive_costs : Query.t -> Logic.term -> bool
val take_lambda_cost : Query.t -> Logic.term -> Language.Metric.t -> lambda_bound option
val lookup_spent : State.frame -> Costs.counter -> Logic.term
val read_condition : State.environment -> Query.t -> Costs.counter -> Types.condition
val spend : State.frame -> (Costs.counter -> Logic.term) -> State.frame
val declare_unknown_amount : State.frame -> Costs.counter -> Logic.term
val make_potential_credit : Query.t -> Logic.term -> Logic.term

val count_declared_potential :
  State.environment -> Query.t -> of_:Types.ty -> Logic.term -> Logic.term

val count_whole_potential : State.environment -> Query.t -> Logic.term -> Logic.term

val spend_operation :
  State.frame ->
  potential_change:(unit -> Logic.term) option ->
  held:(unit -> Types.ty list) ->
  ?note:(Costs.counter -> Logic.term -> unit) ->
  (Costs.counter -> Costs.charge) ->
  State.frame

val spend_quantifier :
  State.frame ->
  count:Logic.term ->
  mark:Query.mark ->
  bound:Logic.symbol ->
  before:State.frame ->
  after:State.frame ->
  State.frame

val enter_body :
  State.frame -> (Costs.counter * Types.condition) list -> body:Mir.body option -> State.frame

val run_without_counters : Query.t -> (unit -> 'a) -> 'a

type lambda_counters

val enter_lambda : State.frame -> Types.function_type -> Mir.body -> lambda_counters * State.frame
val leave_lambda : Query.t -> lambda_counters -> unit

val check_lambda_exits :
  Query.t ->
  lambda_counters ->
  State.frame list ->
  Obligation.location ->
  type_:Types.ty ->
  mark:Query.mark ->
  (Language.Metric.t * lambda_bound) list

val has_another_cost :
  Query.t ->
  Logic.term ->
  captures:Core.local list ->
  bounds:(Language.Metric.t * lambda_bound) list ->
  bool

val note_lambda :
  State.frame ->
  lambda_counters ->
  Logic.term ->
  captures:Core.local list ->
  bounds:(Language.Metric.t * lambda_bound) list ->
  unit
