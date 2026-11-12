val body_of : Definitions.context -> Path.t -> Core.parameter list * Core.block
val bind_local : Lowering.state -> Core.local -> Lir.place -> unit

type bound_name = {
  local : Core.local;
  name : string;
  mode : Types.mode;
  ty : Ground.ty;
  part : Lir.place;
}

type slot = Value_slot of Lir.place | Pointer_slot of Lir.local

val into : Lowering.state -> Core.expression -> Lir.place -> unit
val block_into : Lowering.state -> Core.block -> Lir.place option -> unit
val fill_defaults : Lowering.state -> Lir.local -> Core.parameter list -> unit
