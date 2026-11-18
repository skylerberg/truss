val with_counters : State.scope -> Costs.counter list -> (unit -> 'a) -> 'a
val with_no_costs : State.scope -> (unit -> 'a) -> 'a
val with_terminates : State.scope -> bool -> (unit -> 'a) -> 'a
val with_reading_callback : State.scope -> (unit -> 'a) -> 'a
val with_validating : State.scope -> Types.ty -> (unit -> 'a) -> 'a
val with_instantiating : State.scope -> Path.t -> (unit -> 'a) -> 'a
val with_axiomatizing : State.scope -> Logic.symbol -> (unit -> 'a) -> 'a
val with_ghost_run : State.scope -> (unit -> unit) -> Logic.term list
