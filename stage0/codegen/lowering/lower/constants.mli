type constant = Folded of Lowered.data | Run of Ground.ty

val compile_constant : Definitions.context -> Path.t -> constant
val write_output : Lowering.state -> Lowered.place -> unit
val build_evaluator : Definitions.context -> Path.t -> Emit_c.fragment
val compile_assertion : Definitions.context -> definition:Path.t -> condition:int -> constant

val build_assertion_evaluator :
  Definitions.context -> definition:Path.t -> condition:int -> Emit_c.fragment
