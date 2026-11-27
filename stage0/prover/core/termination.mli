val enter_definition : State.frame -> parameters:Mir.parameter list -> State.frame
val reject_unreached_calls_without_decrease : State.frame -> unit

val check_recursive_call :
  State.frame ->
  Obligation.location ->
  origin:Core.origin ->
  path:Path.t ->
  State.clauses ->
  is_self_call:bool ->
  callee_entry:State.frame ->
  unit

val find_induction_premise :
  State.frame ->
  State.clauses ->
  callee:Path.t ->
  callee_entry:State.frame ->
  argument_at:(int -> Logic.term) ->
  Logic.term option

val find_recursive_callee : State.frame -> Obligation.location -> Path.t option -> Path.t option
val reject_uncompared_recursion : State.frame -> Obligation.location -> Path.t option -> unit

val reject_recursion_through_higher_order_argument :
  State.frame -> Obligation.location -> Mir.statement -> unit

type loop_measure = { read : State.frame -> Logic.term list; at_head : Logic.term list }

val find_written_measures : Mir.loop_clause list -> Mir.formula list option
val read_measures : State.frame -> Mir.formula list -> Logic.term list

val make_comparison_measure :
  State.frame ->
  (Language.Comparison.t * (State.frame -> Logic.term * Logic.term)) option ->
  (State.frame -> Logic.term list) option

val read_loop_measure :
  ?implicit:(State.frame -> Logic.term list) ->
  Mir.loop_clause list ->
  head:State.frame ->
  loop_measure option

val require_measure : State.frame -> Obligation.location -> loop:string -> is_measured:bool -> unit
val check_loop_measure : State.frame -> Obligation.location -> loop_measure option -> unit
