(** The laws of a trait as facts, and a named function passed for a function-typed parameter. *)

val check_callback_requires :
  State.context ->
  State.frame ->
  Invocation.site ->
  ('a * 'b * Invocation.shape) option ->
  State.passed list ->
  unit

val updating_helper : State.context -> Invocation.t -> bool
val laws_key : Types.trait_reference -> Types.ty -> string
val laws_of : State.context -> Path.t -> (State.source * Mir.law) list
val law_parameter_types : substitution:Types.substitution -> Mir.law -> Types.ty list

val law_frame :
  State.frame ->
  State.source ->
  substitution:Types.substitution ->
  Mir.law ->
  Logic.term list ->
  State.frame

val assume_laws :
  State.context -> State.frame -> at:State.span -> Types.trait_reference -> Types.ty -> unit

val template_trait : Path.t
val signature_terminates : State.context -> Path.t -> bool

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
