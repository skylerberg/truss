val find_refused_class : State.state -> sides:(Types.ty * Types.ty) list -> int option
val report_decided_in_specification : State.state -> Core.origin -> int -> Catalog.reported
val list_class_pairs : State.state -> Types.ty * Types.ty -> (int * Types.ty) list

val add_mismatch_diagnostic :
  State.state ->
  Core.origin ->
  sides:(Types.ty * Types.ty) list ->
  Catalog.Inference.mismatch ->
  Catalog.reported

val add_operand_mismatch :
  State.state ->
  at:Core.origin ->
  left:Core.origin * Types.ty ->
  right:Core.origin * Types.ty ->
  Catalog.reported

val report_mismatch :
  ?copy:Catalog.Inference.view_copy ->
  State.state ->
  Core.origin ->
  expected:Types.ty ->
  actual:Types.ty ->
  unit

val report_requirement :
  State.state ->
  State.goal ->
  ?associated:string * Types.ty * Types.ty ->
  impl_need:Catalog.Inference.impl_need option ->
  Types.ty ->
  Catalog.reported

val report_failure :
  State.state ->
  State.goal ->
  ?associated:string * Types.ty * Types.ty ->
  Types.ty ->
  Catalog.reported
