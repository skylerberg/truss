val make_state : unit -> State.lending_state
val enter_method : State.context -> part_type:Types.ty -> unit
val holds_where_lent : Mir.formula -> bool
val find_part_sort : State.context -> Logic.sort option

val lend_part :
  State.context ->
  State.frame ->
  Core.origin ->
  Language.Mode.t ->
  handed:Logic.term ->
  lends_places:bool ->
  write_back:(State.frame -> Logic.term -> State.frame) ->
  State.frame

val list_lent_parts : State.context -> State.lent_part list
val bind_final : State.frame -> Logic.term -> State.frame
val read_final_result : State.frame -> Logic.term
