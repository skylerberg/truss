val list_laws : State.environment -> Path.t -> (State.source * Mir.law) list
val list_law_parameter_types : substitution:Types.substitution -> Mir.law -> Types.ty list

val bind_law_parameters :
  State.frame ->
  State.source ->
  substitution:Types.substitution ->
  Mir.law ->
  Logic.term list ->
  State.frame

val assume_laws : State.context -> State.frame -> Types.trait_reference -> Types.ty -> unit
