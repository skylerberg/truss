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

val find_recursive_callee :
  State.context -> State.frame -> Obligation.location -> Path.t option -> Path.t option

val reject_uncompared_recursion :
  State.context -> State.frame -> Obligation.location -> Path.t option -> unit

val reject_recursion_through_supplied_code :
  State.context -> State.frame -> Obligation.location -> Mir.statement -> unit

val make_state : terminates:bool -> measures:Mir.formula list -> State.termination_state
val run_in_lambda : State.context -> Types.function_type -> (unit -> 'a) -> 'a

type loop_measure = { read : State.frame -> Logic.term list; at_head : Logic.term list }

val find_written_measures : Mir.loop_clause list -> Mir.formula list option
val read_measures : State.context -> State.frame -> Mir.formula list -> Logic.term list

val make_comparison_measure :
  State.context ->
  (Language.Comparison.t * (State.frame -> Logic.term * Logic.term)) option ->
  (State.frame -> Logic.term list) option

val read_loop_measure :
  ?implicit:(State.frame -> Logic.term list) ->
  State.context ->
  Mir.loop_clause list ->
  head:State.frame ->
  loop_measure option

val require_measure : State.context -> loop:string -> is_measured:bool -> unit
val check_loop_measure : State.frame -> Obligation.location -> loop_measure option -> unit
