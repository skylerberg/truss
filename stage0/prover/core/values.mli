val note_unfinished : State.frame -> unit
val run_ghost_code : State.frame -> Mir.t -> Logic.term
val assume_extensional : State.frame -> Types.ty -> Logic.term -> Logic.term -> unit

val apply_list_literal :
  State.frame -> Invocation.site -> Logic.term list -> State.frame * Logic.term

val apply_map_literal :
  State.frame ->
  ty:Types.ty ->
  location:Obligation.location ->
  (Core.origin option * Logic.term * Logic.term) list ->
  State.frame * Logic.term

val make_literal_value : State.frame -> Types.ty -> Language.Literal.t -> Logic.term

val project_field :
  State.frame -> Types.ty -> string option -> string -> Types.ty -> Logic.term -> Logic.term

val evaluate_constant : State.frame -> Path.t -> Types.substitution -> Logic.term

val apply_construct :
  State.frame ->
  Invocation.site ->
  string option ->
  (string * Logic.term) list ->
  State.frame * Logic.term

val make_text_match :
  State.environment ->
  Query.t ->
  Obligation.location ->
  Types.ty ->
  Logic.term ->
  string ->
  Logic.term

val apply_specification_function :
  State.frame ->
  location:Obligation.location ->
  Core.specification_function ->
  Logic.term list ->
  unconverted:Types.ty list ->
  types:Types.ty list ->
  State.frame * Logic.term
