type argument = Context.argument = Place of Lowered.place | Value of Lowered.operand
type types = Context.types = { uint64 : Ground.ty; string : Ground.ty }

val list_consumed_places : Intrinsic.operation -> int list

val lower :
  ?value_arguments:Z.t list ->
  ?reported:Lowered.operand ->
  Memory_layout.env ->
  Emit_c.Ir_builder.t ->
  types ->
  Intrinsic.operation ->
  type_arguments:Ground.ty list ->
  argument list ->
  destination:Lowered.place option ->
  site:Lowered.site ->
  trace:Lowered.operand option ->
  Lowered.place option
