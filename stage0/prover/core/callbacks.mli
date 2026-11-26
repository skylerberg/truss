val make_state : unit -> State.callback_state
val declare_own : State.context -> (Core.local * string * Mir.callback) list -> unit
val run_reading_callback : State.context -> (unit -> 'a) -> 'a
val find_own_callback : State.context -> Core.local -> (string * Mir.callback) option

val apply_function :
  State.context -> Types.function_type -> Logic.term -> Logic.term list -> Logic.term

val returns_value : Types.function_type -> bool
val is_in_the_logic : Types.function_type -> bool

val make_input_variables :
  State.context ->
  Types.function_type ->
  label:string ->
  numbers:int list ->
  (Logic.symbol * Logic.sort) list

type relation_variables = {
  inputs : (Logic.symbol * Logic.sort) list;
  changed : (int * (Logic.symbol * Logic.sort)) list;
  returned : (Logic.symbol * Logic.sort) list;
  entries : Logic.term list;
  exits : Logic.term list;
  result : Logic.term;
}

val make_relation_variables :
  State.context -> Types.function_type -> label:string -> numbers:int list -> relation_variables

val make_callback_ensures :
  State.context ->
  Types.function_type ->
  Logic.term ->
  entries:Logic.term list ->
  exits:Logic.term list ->
  result:Logic.term ->
  Logic.term

val apply_callback_ensures : State.context -> Types.function_type -> Logic.term list -> Logic.term
val find_logic_link : State.context -> Types.function_type -> Logic.term -> Logic.term option

type parameter_contract = (State.source * State.frame * Mir.callback) option

val read_requires :
  State.context ->
  parameter_contract ->
  Logic.term list ->
  (Catalog.Prover.quoted * Logic.term) list

val read_ensures :
  State.context ->
  parameter_contract ->
  entries:Logic.term list ->
  exits:Logic.term list ->
  result:Logic.term ->
  (Catalog.Prover.quoted * Logic.term) list

val read_named_function :
  State.context ->
  State.frame ->
  Invocation.site ->
  Path.t ->
  Types.instantiation ->
  is_argument:bool ->
  Logic.term

val check_escaping_callback : State.context -> State.frame -> Core.local -> unit

val check_passed :
  State.context ->
  State.frame ->
  Invocation.site ->
  Callee.t ->
  State.passed ->
  arguments:(int * Logic.term) list ->
  unit

val check_called :
  State.context -> State.frame -> Invocation.site -> Invocation.shape -> Logic.term list -> unit

val assume_returned :
  State.context ->
  State.frame ->
  Types.function_type ->
  Logic.term ->
  Invocation.shape ->
  entries:Logic.term list ->
  exits:Logic.term list ->
  result:Logic.term ->
  unit
