type evaluated = Folded of Lowered.data | Run of Ground.ty

val compile : Definitions.context -> Lowered.Item.t -> evaluated
val build_evaluator : Definitions.context -> Lowered.Item.t -> Emit_c.fragment
