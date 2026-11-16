val real_implementations :
  Lowering.state -> user:string -> Path.t list -> (Path.t * Lowered.operand) list

val lower : Definitions.context -> Instance.generated -> Emit_c.Builder.instance
val lower_table : Definitions.context -> Instance.table -> Lowered.table
