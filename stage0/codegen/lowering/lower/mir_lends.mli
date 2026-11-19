val obtain_lent_call : Lowering.state -> Mir.local -> Lowering.lent_call
val emit_mark : Lowering.state -> Lowered.intrinsic -> Lowering.lent_call -> unit
val find_forwarded_call : Lowering.state -> Mir.call -> Forwarded.t option
val is_forwarded_whole : Lowering.mir_frame -> Mir.local -> bool
val make_owned_locals : Lowering.state -> unit

val outlives_call :
  owns:(Mir.local -> bool) -> is_view:(Types.ty -> bool) -> Mir.Graph.body -> Mir.place -> bool
