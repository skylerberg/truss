val check_callback_requires :
  State.context ->
  State.frame ->
  Invocation.site ->
  ('a * 'b * Invocation.shape) option ->
  State.passed list ->
  unit

val calls_updating_helper : State.context -> Invocation.t -> bool
val list_laws : State.context -> Path.t -> (State.source * Mir.law) list
val list_law_parameter_types : substitution:Types.substitution -> Mir.law -> Types.ty list

val bind_law_parameters :
  State.frame ->
  State.source ->
  substitution:Types.substitution ->
  Mir.law ->
  Logic.term list ->
  State.frame

val assume_laws :
  State.context -> State.frame -> at:State.location -> Types.trait_reference -> Types.ty -> unit

val template_trait : Path.t
val has_method_time : State.context -> Invocation.callee -> Path.t -> bool

val check_named_callback :
  State.context ->
  State.frame ->
  Invocation.t ->
  State.passed ->
  origin:int ->
  Path.t ->
  State.contract ->
  State.passed list ->
  unit
