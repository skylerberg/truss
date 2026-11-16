type unsupported = { construct : string; at : Lowered.site option }

exception Unsupported of unsupported

type context

val env : context -> Memory_layout.env
val drop_and_copy : context -> Drop_and_copy.t
val monomorphic : Interface.Lookups.t -> Monomorphic.context
val context : Lookups.settings -> env:Memory_layout.env -> Lookups.t -> context

val lower_source_code :
  context -> path:Path.t -> type_arguments:Ground.argument list -> Emit_c.Builder.instance

val lower_generated : context -> Instance.generated -> Emit_c.Builder.instance

type constant = Folded of Lowered.data | Run of Ground.ty

val lower_constant : context -> Path.t -> constant
val lower_evaluator : context -> Path.t -> Emit_c.Builder.instance
val lower_table : context -> Instance.table -> Lowered.table
val test_key : Path.t -> Instance.key

val lower_template_check :
  context ->
  from_template:Path.t ->
  literals:string list ->
  clauses:int list ->
  Emit_c.Builder.instance

val lower_call_evaluation :
  context -> function_:Path.t -> arguments:Z.t list -> Emit_c.Builder.instance
