type while_loop = {
  while_at : Core.origin;
  while_clauses : Mir.loop_clause list;
  changed : State.changed_part list;
  bind_parts : State.frame -> State.frame;
  test : State.frame -> (State.frame * Logic.term) option;
  run_body : State.frame -> State.frame list * State.frame list;
  on_failure : State.frame -> State.frame option;
  measure_operands : (Language.Comparison.t * (State.frame -> Logic.term * Logic.term)) option;
}

type iterable =
  | Over_range of { low : Logic.term; high : Logic.term; inclusive : bool }
  | Over_cursor of {
      cursor : State.passed_place;
      cursor_type : Types.ty;
      next : Invocation.t;
      next_origin : Core.origin;
    }

type for_loop = {
  for_at : Core.origin;
  for_clauses : Mir.loop_clause list;
  iterable : iterable;
  element_type : Types.ty;
  lent_element : Types.ty option;
  invariant_count : (State.frame -> Logic.term) option;
  collection : (State.frame -> Types.ty * Logic.term) option;
  element_call : (State.frame -> Logic.term) option;
  bind_element : State.frame -> Logic.term -> State.frame;
  compute_changed_in : State.frame -> State.changed_part list;
  compute_changed_by_body : State.frame -> State.changed_part list;
  run_body : State.frame -> Logic.term -> State.frame list * State.frame list;
  bind_parts : State.frame -> State.frame;
}

val havoc : State.context -> State.frame -> State.changed_part list -> State.frame
val keep_holding_clauses : State.context -> Mir.loop_clause list -> Mir.loop_clause list
val run_while_loop : State.context -> State.frame -> while_loop -> State.frame option
val run_for_loop : State.context -> State.frame -> for_loop -> State.frame option
