type argument = Place of Lowered.place | Value of Lowered.operand
type types = { uint64 : Ground.ty; string_slice : Ground.ty }

val list_consumed_places : Intrinsic.operation -> int list

val lower :
  ?checks:bool ->
  ?value_arguments:Z.t list ->
  ?reported:Lowered.operand ->
  Memory_layout.env ->
  Emit_c.Builder.t ->
  types ->
  Intrinsic.operation ->
  type_arguments:Ground.ty list ->
  argument list ->
  destination:Lowered.place option ->
  site:Lowered.site ->
  Lowered.place option
