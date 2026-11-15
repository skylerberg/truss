type constant = Folded of Lowered.data | Run of Ground.ty

val call_depth : int
val write_fully : Path.t
val constant : Definitions.context -> Path.t -> constant
val write_output : Lowering.state -> Lowered.place -> unit
val evaluator : Definitions.context -> Path.t -> Emit_c.Builder.instance
