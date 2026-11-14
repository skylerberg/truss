(** Loops: invariants, measures, and costs, at the head, after each iteration, and at the exit. *)

val loop_head :
  State.context ->
  State.frame ->
  State.loop_cost list ->
  iterations:Logic.term option ->
  State.frame

val loop_iterations :
  State.context ->
  int ->
  State.frame ->
  State.loop_cost list ->
  mark:int ->
  facts:Logic.term list ->
  ends:State.frame list ->
  breaks:State.frame list ->
  unit

val loop_exit :
  State.context ->
  State.frame ->
  State.loop_cost list ->
  iterations:Logic.term option ->
  most:Logic.term list ->
  State.frame

val assertion :
  State.context -> State.frame -> origin:int -> bit_vector:Mir.formula option -> Logic.term -> unit

val lend_part :
  State.context ->
  State.frame ->
  int ->
  Types.mode ->
  handed:Logic.term ->
  lends:bool ->
  write_back:(State.frame -> Logic.term -> State.frame) ->
  State.frame option

val element_written_back :
  State.context ->
  State.frame ->
  operation:Intrinsic.operation ->
  type_arguments:Types.argument list ->
  receiver:State.passed_place ->
  receiver_type:Types.ty ->
  Logic.term ->
  Logic.term ->
  State.frame

val field_replaced :
  State.context -> Types.ty -> string option -> string -> Logic.term -> Logic.term -> Logic.term

val check_preserved_validity :
  State.context ->
  State.frame ->
  State.span ->
  (string * Types.ty * Logic.term * (State.frame -> Logic.term option)) list ->
  unit

val check_invariants : State.context -> State.frame -> Mir.loop_clause list -> when_:string -> unit
val assume_invariants : State.context -> State.frame -> Mir.loop_clause list -> unit
val measures_of : Mir.loop_clause list -> Mir.formula list option

val enter_loop :
  ?holds:State.changed ->
  State.context ->
  State.frame ->
  entry:State.frame ->
  Mir.loop_clause list ->
  changed:State.changed ->
  State.loop_start

val iterations_so_far : State.context -> State.frame -> State.loop_cost list -> Logic.term option
val one_step : Costs.counter -> Logic.term
val for_ : driven:State.driven -> State.context -> State.frame -> State.frame option
