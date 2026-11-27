val bind_own : State.frame -> (Core.local * string * Mir.callback) list -> State.frame
val apply_function : Types.function_type -> Logic.term -> Logic.term list -> Logic.term
val returns_value : Types.function_type -> bool
val is_in_the_logic : Types.function_type -> bool

val make_input_variables :
  Types.function_type -> label:string -> numbers:int list -> (Logic.symbol * Logic.sort) list

type relation_variables = {
  inputs : (Logic.symbol * Logic.sort) list;
  changed : (int * (Logic.symbol * Logic.sort)) list;
  returned : (Logic.symbol * Logic.sort) list;
  entries : Logic.term list;
  exits : Logic.term list;
  result : Logic.term;
}

val make_relation_variables :
  Types.function_type -> label:string -> numbers:int list -> relation_variables

val make_callback_ensures :
  Types.function_type ->
  Logic.term ->
  entries:Logic.term list ->
  exits:Logic.term list ->
  result:Logic.term ->
  Logic.term

val apply_callback_ensures : Types.function_type -> Logic.term list -> Logic.term
val find_logic_link : Types.function_type -> Logic.term -> Logic.term option

type parameter_contract = (State.source * State.frame * Mir.callback) option

val read_requires :
  parameter_contract -> Logic.term list -> (Catalog.Prover.quoted * Logic.term) list

val read_ensures :
  parameter_contract ->
  entries:Logic.term list ->
  exits:Logic.term list ->
  result:Logic.term ->
  (Catalog.Prover.quoted * Logic.term) list

val read_named_function :
  State.frame -> Invocation.site -> Path.t -> Types.instantiation -> is_argument:bool -> Logic.term

val check_read : State.frame -> Logic.term -> unit

val check_passed :
  State.frame ->
  at:Core.origin ->
  Callee.t ->
  State.passed ->
  arguments:(int * Logic.term) list ->
  unit

val oblige_requires : State.frame -> Invocation.site -> Logic.term -> Logic.term list -> Logic.term

val assume_returned :
  State.frame ->
  Types.function_type ->
  Logic.term ->
  entries:Logic.term list ->
  exits:Logic.term list ->
  result:Logic.term ->
  unit
