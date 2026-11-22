type unsupported = { construct : string; at : Lowered.site option }

exception Unsupported of unsupported

type context

val env : context -> Memory_layout.env
val drop_and_copy : context -> Drop_and_copy.t
val make_monomorphic_context : Interface.Lookups.t -> Monomorphic.context
val make_context : env:Memory_layout.env -> Lookups.t -> context

val lower_source_code :
  context ->
  path:Path.t ->
  instantiation:Ground.instantiation ->
  assumes_condition:bool ->
  Emit_c.fragment

val lower_generated : context -> Lowered.Item.generated -> Emit_c.fragment

type constant = Folded of Lowered.data | Run of Ground.ty

val lower_constant : context -> Path.t -> constant
val lower_evaluator : context -> Path.t -> Emit_c.fragment
val lower_assertion : context -> definition:Path.t -> condition:int -> constant
val lower_assertion_evaluator : context -> definition:Path.t -> condition:int -> Emit_c.fragment
val lower_table : context -> Lowered.Item.table -> Lowered.table

val lower_call_evaluation :
  context -> function_:Path.t -> arguments:Lowered.Item.argument list -> Emit_c.fragment
