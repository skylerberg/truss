val is_in_recursion_group : State.environment -> Path.t -> bool
val find_group_member : State.frame -> 'operand Core.target -> Path.t option
val is_in_proof_cycle : State.environment -> Path.t -> bool
val is_evaluated_constant : State.environment -> Path.t -> Mir.t -> bool
val reject_constant_cycle : State.frame -> Mir.t -> unit

type circular_proof

val list_circular_clauses : State.frame -> type_:Types.ty -> circular_proof list
val list_circular_proofs : State.frame -> circular_proof list
val reject_circular_proof : State.frame -> circular_proof -> unit
