val build : Language.Mode.t -> Core.expression -> Core.operand
val build_argument : Language.Mode.t -> Core.expression -> Core.argument

val build_default :
  make:(Types.ty -> Core.kind -> Core.expression) -> Language.Mode.t -> Core.place -> Core.operand

val make_field_default :
  Interface.Lookups.t ->
  origin:Core.origin ->
  type_:Path.t ->
  type_arguments:Types.argument list ->
  variant:string option ->
  Types.field ->
  Core.place
