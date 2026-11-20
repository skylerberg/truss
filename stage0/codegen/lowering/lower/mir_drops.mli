type entry = {
  evidence : (Path.t * Lowered.operand) list;
  provides : (Path.t * Lowered.operand) list list;
}

type region = {
  region_frame : Lowering.frame;
  region_body : Lowering.mir_frame;
  lowered : (Mir.Graph.block, Lowered.block) Hashtbl.t;
  mutable pending : (Mir.Graph.block * Lowered.block * entry) list;
  depth : int;
  start : entry;
  enclosing : region option;
  ending : (Core.id * Lowered.block) option;
}

val make_region : ?ending:Core.id * Lowered.block -> ?enclosing:region -> Lowering.state -> region
val restore : Lowering.state -> entry -> unit
val resolve_jump : ?entry:entry -> Lowering.state -> region -> Mir.Graph.block -> Lowered.block
val claim : Lowering.state -> region -> Mir.Graph.block -> unit
val goto : Lowering.state -> region -> Mir.Graph.block -> unit
val continue_loop : Lowering.state -> unit
val break_loop : Lowering.state -> unit
val update_flags : Lowering.state -> before:Moves.state -> unit
val drop_overwritten : Lowering.state -> Mir.place -> Lowered.place -> Ground.ty -> unit
val return_from_frame : Lowering.state -> unit
val end_local : Lowering.state -> Mir.local -> unit
