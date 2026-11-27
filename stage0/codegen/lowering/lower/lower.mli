type unsupported = { construct : Catalog.Codegen.construct; at : Lowered.site option }

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
  assumed:Path.t list ->
  Emit_c.fragment

val lower_generated : context -> Lowered.Item.generated -> Emit_c.fragment

type evaluated = Folded of Lowered.data | Run of Ground.ty

val lower_evaluated : context -> Lowered.Item.t -> evaluated
val lower_evaluator : context -> Lowered.Item.t -> Emit_c.fragment
val lower_table : context -> Lowered.Item.table -> Lowered.table
