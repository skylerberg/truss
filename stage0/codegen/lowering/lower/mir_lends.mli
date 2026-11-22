val obtain_lend_record : Lowering.state -> Mir.local -> Lowered.operand
val obtain_lend_arena : Lowering.state -> Lowered.operand
val end_lend : Lowering.state -> Mir.local -> unit
val transfer_lends : Lowering.state -> Lowering.lending -> unit
val find_forwarded_call : Lowering.state -> Mir.call -> Forwarded.t option
val is_forwarded_whole : Lowering.mir_frame -> Mir.local -> bool
val make_owned_locals : Lowering.state -> unit

val outlives_call :
  owns:(Mir.local -> bool) -> is_view:(Types.ty -> bool) -> Mir.Graph.body -> Mir.place -> bool
