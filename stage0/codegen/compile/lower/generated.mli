val entry : Definitions.context -> Instance.key -> Instance.key -> Lir.t
val locked_entry : Definitions.context -> Instance.key -> capability:Path.t -> name:string -> Lir.t
val locked_table : Definitions.context -> Instance.key -> capability:Path.t -> Lir.table
val table : Definitions.context -> Instance.key -> Lir.table

val real_implementations :
  Lowering.state -> user:string -> Path.t list -> (Path.t * Lir.operand) list

val program_main : Definitions.context -> Instance.key -> Path.t -> Lir.t

val adapter :
  Definitions.context -> Instance.key -> function_:Instance.key -> ty:Ground.function_type -> Lir.t

val any_entry : Definitions.context -> Instance.key -> Instance.key -> Lir.t
val any_table : Definitions.context -> Instance.key -> Lir.table
