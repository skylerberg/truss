type constant = Folded of Lowered.data | Run of Ground.ty

val constant : Definitions.context -> Path.t -> constant
val begin_output : Lowering.state -> Lowered.place
val write_output : Lowering.state -> Lowered.place -> unit
val evaluator : Definitions.context -> Path.t -> Emit_c.Builder.instance
