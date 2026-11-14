val entry : Definitions.context -> Instance.key -> Instance.key -> Emit_c.Builder.instance

val locked_entry :
  Definitions.context -> Instance.key -> capability:Path.t -> name:string -> Emit_c.Builder.instance

val locked_table : Definitions.context -> Instance.key -> capability:Path.t -> Lowered.table
val table : Definitions.context -> Instance.key -> Lowered.table

val real_implementations :
  Lowering.state -> user:string -> Path.t list -> (Path.t * Lowered.operand) list

val program_main : Definitions.context -> Instance.key -> Path.t -> Emit_c.Builder.instance

val adapter :
  Definitions.context ->
  Instance.key ->
  function_:Instance.key ->
  ty:Ground.function_type ->
  Emit_c.Builder.instance

val any_entry : Definitions.context -> Instance.key -> Instance.key -> Emit_c.Builder.instance
val any_table : Definitions.context -> Instance.key -> Lowered.table
