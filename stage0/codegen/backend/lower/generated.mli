val list_real_implementations :
  Lowering.state -> user:string -> Path.t list -> (Path.t * Lowered.operand) list

val lower : Definitions.context -> Lowered.Item.generated -> Emit_c.Builder.item_code
val lower_table : Definitions.context -> Lowered.Item.table -> Lowered.table
