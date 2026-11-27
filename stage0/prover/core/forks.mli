type exit = { exited : State.frame; exit_locals : Locals.local list }

type branch = {
  read : State.frame -> State.frame option * exit list;
  read_end : State.frame -> State.frame option;
  list_changed_parts : State.frame -> State.changed_part list;
}

val read : State.frame -> concurrent:bool -> branch list -> State.frame option
