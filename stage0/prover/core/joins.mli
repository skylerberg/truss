val name_path_condition : State.frame -> Logic.term -> Logic.term

val merge :
  ?value_type:Types.ty ->
  condition:Logic.term ->
  (Logic.term * State.frame * Logic.term option) list ->
  State.frame * Logic.term option

val join :
  ?value_type:Types.ty ->
  (State.frame * Logic.term option) list ->
  (State.frame * Logic.term option) option

val join_frames : State.frame list -> State.frame option
