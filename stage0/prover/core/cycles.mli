val is_in_recursion_group : State.context -> Path.t -> bool
val find_group_member : State.context -> State.frame -> 'operand Core.target -> Path.t option
val is_in_proof_cycle : State.context -> Path.t -> bool
val is_evaluated_constant : State.context -> Path.t -> Mir.t -> bool
val reject_constant_cycle : State.context -> State.frame -> Mir.t -> unit

type circular_proof

val list_circular_clauses : State.context -> State.frame -> type_:Types.ty -> circular_proof list
val list_circular_contracts : State.context -> State.frame -> circular_proof list
val list_circular_laws : State.context -> State.frame -> circular_proof list
val reject_circular_proof : State.context -> State.frame -> circular_proof -> unit
