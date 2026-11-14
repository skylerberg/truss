type constant = Folded of Lir.data | Run of Ground.ty

val constant : Definitions.context -> Path.t -> constant
val begin_output : Lowering.state -> Lir.place
val write_output : Lowering.state -> Lir.place -> unit
val evaluator : Definitions.context -> Path.t -> Emit_c.Builder.instance
