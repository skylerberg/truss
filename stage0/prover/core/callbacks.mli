val make_state : unit -> State.callback_state
val declare_own : State.context -> (Core.local * string * Mir.callback) list -> unit
val is_reading : State.context -> bool

val apply_function :
  State.context -> Types.function_type -> Logic.term -> Logic.term list -> Logic.term

val returns_value : Types.function_type -> bool
val is_in_the_logic : Types.function_type -> bool

val make_callback_ensures :
  State.context ->
  Types.function_type ->
  Logic.term ->
  entries:Logic.term list ->
  exits:Logic.term list ->
  result:Logic.term ->
  Logic.term

val apply_callback_ensures : State.context -> Types.function_type -> Logic.term list -> Logic.term

val declare_callback_arguments :
  State.context -> State.frame -> ('a * Types.ty) list -> Logic.term list

val make_callback_contract_frame : State.frame -> Core.local list -> Logic.term list -> State.frame
val find_own_callback : State.context -> Core.local -> (string * Mir.callback) option
val check_escaping_callback : State.context -> State.frame -> Core.local -> unit
val run_reading_callback : State.context -> (unit -> 'a) -> 'a

val list_callback_facts :
  State.context ->
  State.frame ->
  Invocation.t ->
  int ->
  (int * Logic.term) list ->
  Logic.term list ->
  Logic.term list

val find_parameter_type : State.context -> State.frame -> Invocation.t -> int -> Types.ty option

val list_callback_promises :
  State.context ->
  State.frame ->
  Invocation.t ->
  int ->
  (int * Logic.term) list ->
  entries:Logic.term list ->
  exits:Logic.term list ->
  result:Logic.term ->
  (Catalog.Prover.quoted * Logic.term) list

val assume_own_callback_ensures :
  State.context ->
  State.frame ->
  Core.local ->
  entries:Logic.term list ->
  exits:Logic.term list ->
  result:Logic.term ->
  unit

val check_callback_promises :
  State.context ->
  State.frame ->
  location:Obligation.location ->
  Invocation.t ->
  State.passed ->
  unpromised:Catalog.Prover.unpromised ->
  assume:
    (State.frame ->
    Types.function_type ->
    entries:Logic.term list ->
    exits:Logic.term list ->
    result:Logic.term ->
    unit) ->
  State.passed list ->
  unit

val assume_nothing :
  State.frame ->
  Types.function_type ->
  entries:Logic.term list ->
  exits:Logic.term list ->
  result:Logic.term ->
  unit

val check_forwarded_callback :
  State.context ->
  State.frame ->
  Invocation.site ->
  Invocation.t ->
  State.passed ->
  Core.local ->
  State.passed list ->
  unit

val check_callback_requires :
  State.context ->
  State.frame ->
  Invocation.site ->
  ('a * 'b * Invocation.shape) option ->
  State.passed list ->
  unit

val check_named_callback :
  State.context ->
  State.frame ->
  Invocation.t ->
  State.passed ->
  origin:Core.origin ->
  Path.t ->
  State.contract ->
  State.passed list ->
  unit
