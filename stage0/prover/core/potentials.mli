val has_potential : State.context -> ?seen:Types.ty list -> Types.ty -> bool

val compute_potential :
  State.context -> State.frame -> ?seen:Types.ty list -> Types.ty -> Logic.term -> Logic.term

val compute_arguments_potential_change :
  State.context ->
  before:State.frame ->
  after:State.frame ->
  State.passed list ->
  changed:(int * Logic.term) list ->
  Logic.term

val compute_call_potential_change :
  State.context ->
  before:State.frame ->
  after:State.frame ->
  State.passed list ->
  changed:(int * Logic.term) list ->
  result_type:Types.ty ->
  result:Logic.term ->
  Logic.term

val compute_elements_potential : State.context -> Types.ty -> Logic.term -> Logic.term

val assume_element_potential_change :
  State.context ->
  State.frame ->
  Types.ty ->
  before:Logic.term ->
  after:Logic.term ->
  replaced:Logic.term ->
  written:Logic.term ->
  unit

val find_buffer : State.context -> Types.ty -> State.buffer option
val find_declared_element : Types.ty -> erased:Types.ty -> Types.ty

val list_declared_fields :
  State.context -> Types.ty -> ((string option * string) * Types.ty) list option

val spend_declared_potential : State.context -> State.frame -> Types.ty -> Logic.term -> State.frame

val spend_enclosing_change :
  State.context ->
  before:State.frame ->
  after:State.frame ->
  (Logic.term * Mir.place) list ->
  place_type:(State.frame -> Mir.place -> Types.ty) ->
  read:(State.frame -> Mir.place -> Logic.term) ->
  State.frame

val spend_forgotten :
  State.context ->
  (Locals.local * Types.ty) list ->
  before:State.frame ->
  after:State.frame ->
  State.frame

val spend_provided : State.context -> State.frame -> Logic.term Lazy.t -> State.frame
