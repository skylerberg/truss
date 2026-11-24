val ground_instantiation : Lowering.state -> Types.instantiation -> Ground.instantiation
val resolve_item : Lowering.state -> Mir.callee -> Path.t * Ground.instantiation

val read_callee_signature :
  Lowering.state -> Path.t -> Ground.instantiation -> Types.signature * Types.substitution

val compute_result_type : Lowering.state -> Mir.callee -> Ground.ty

val lower_call_with_places :
  Lowering.state ->
  Mir.callee ->
  Lowered.place list ->
  destination:Lowered.place ->
  site:Lowered.site option ->
  unit

val evaluate_arguments :
  Lowering.state ->
  Types.signature ->
  Types.substitution ->
  Mir.argument list ->
  (Language.Mode.t * Ground.ty * Lowered.place) list

val lower_argument_place :
  Lowering.state -> Mir.argument -> Language.Mode.t * Ground.ty * Lowered.place

val lower_intrinsic :
  Lowering.state ->
  ?reported:Lowered.operand ->
  Intrinsic.operation ->
  type_arguments:Types.argument list ->
  Mir.argument list ->
  destination:Lowered.place option ->
  site:Lowered.site ->
  Lowered.place option

val read_field_default :
  Lowering.state ->
  Ground.ty ->
  variant:string option ->
  field:string ->
  Mir.Graph.t Mir.field_default Mir.sourced
