type decision = Always | In_run of Types.condition | Elsewhere

val implies : Lookups.t -> current:Path.t -> Types.condition -> Types.condition -> bool

val may_panic :
  Lookups.t -> current:Path.t -> condition:Types.condition -> Types.capability_set -> bool

val may_panic_for_every_value :
  Lookups.t -> current:Path.t -> condition:Types.condition -> Types.capability_set -> bool

val decide : State.context -> substitution:Types.substitution -> Types.condition -> decision
val holds_here : State.context -> ?substitution:Types.substitution -> Types.condition -> bool
val find_obligation_condition : decision -> Types.condition option
val with_obligation_condition : State.context -> Types.condition -> (unit -> 'a) -> 'a
