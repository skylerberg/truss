val require_mir_frame : Lowering.state -> Lowering.mir_frame
val read_mir_graph : Definitions.context -> Path.t -> Mir.Graph.t
val read_parameter_defaults : Definitions.context -> Path.t -> (int * Mir.Graph.t) list Mir.sourced
val extract_parameter : Mir.Graph.body -> int -> Types.mode * string option * Types.ty
val read_spans : Lowering.state -> Source.Definition_span.t array
val locate_site : Lowering.state -> Core.origin -> Lowered.site
val find_reported_site : Lowering.state -> Lowered.operand option
val lookup_local_info : Lowering.state -> int -> Mir.local_info
val bind_local : Lowering.state -> Mir.local -> Lowered.place -> unit
val find_result_slot : Lowering.state -> Lowered.place option
val lookup_local_place : Lowering.state -> Mir.local -> Lowered.place
val convert_comparison : Core.comparison -> Lowered.comparison
val ground_argument : Lowering.state -> Types.argument -> Ground.argument
val split_arguments : Lowering.state -> Types.argument list -> Ground.ty list * Z.t list
val lower_place : Lowering.state -> Mir.place -> Lowered.place
val list_variants : Lowering.state -> Ground.ty -> (string option * (string * Ground.ty) list) list

val make_body_frame :
  Lowering.state ->
  ?owner:Lowering.scope ->
  ?returns_into:Lowered.place ->
  ?lending:Lowering.lending ->
  ?passed:Ground.mode list ->
  lambdas:Mir.Graph.body array ->
  Mir.Graph.body ->
  Lowering.mir_frame

val make_field_projection : string option -> string -> Lowered.projection
val compute_operand_type : Lowering.state -> Mir.operand -> Ground.ty
val lower_operand : Lowering.state -> Mir.operand -> Lowered.operand
val lower_operand_place : Lowering.state -> Mir.operand -> Lowered.place
val write_operand : Lowering.state -> Mir.operand -> Lowered.place -> unit
val make_discard_place : Lowering.state -> Lowered.place
val compute_target_type : Lowering.state -> Mir.place -> Mir.rvalue -> Ground.ty
val reads : Mir.rvalue -> Mir.local -> bool
val alias : Lowering.state -> Mir.local -> Lowered.place -> writable:bool -> unit
