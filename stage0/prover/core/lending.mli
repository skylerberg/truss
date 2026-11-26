val holds_where_lent : Mir.formula -> bool

val lend_part :
  State.frame ->
  Core.origin ->
  Language.Mode.t ->
  handed:Logic.term ->
  lends_places:bool ->
  write_back:(State.frame -> Logic.term -> State.frame) ->
  State.lent_part * State.frame

val bind_final : State.frame -> Logic.term -> State.frame
val read_final_result : State.frame -> Logic.term
