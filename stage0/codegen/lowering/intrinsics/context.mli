val raise_bug : ('a, unit, string, 'b) format4 -> 'a

type argument = Place of Lowered.place | Value of Lowered.operand
type types = { uint64 : Ground.ty; string_slice : Ground.ty }

type t = {
  env : Memory_layout.env;
  builder : Emit_c.Ir_builder.t;
  types : types;
  operation : Intrinsic.operation;
  type_arguments : Ground.ty list;
  value_arguments : Z.t list;
  arguments : argument list;
  destination : Lowered.place option;
  site : Lowered.site;
  reported : Lowered.operand option;
  trace : Lowered.operand option;
}

val make_operand : argument -> Lowered.operand
val read : argument -> Lowered.place
val classify_scalar : Memory_layout.env -> Ground.ty -> Memory_layout.scalar
val set : t -> Lowered.rvalue -> unit
val read_argument : t -> int -> argument
val read_operand : t -> int -> Lowered.operand
val read_place : t -> int -> Lowered.place
val read_type_argument : t -> int -> Ground.ty
val call : t -> ?result:Lowered.place -> Lowered.intrinsic -> Lowered.operand list -> unit
val allocate_uint64_local : t -> Lowered.local
val emit_uint64 : t -> Lowered.rvalue -> Lowered.operand
val emit_bool : t -> Lowered.rvalue -> Lowered.operand
val copy_length : Lowered.place -> Lowered.operand
val panic_with_message : t -> message:Lowered.operand -> length:Lowered.operand -> unit
val panic : t -> string -> unit
val panic_when : t -> Emit_c.Ir_builder.condition -> string -> unit
val fail_obligation_when : t -> Emit_c.Ir_builder.condition -> string -> unit
val fail_operation_when : t -> Emit_c.Ir_builder.condition -> string -> unit
val check_index : t -> Lowered.operand -> Lowered.operand -> unit
val compute_room : t -> Lowered.place -> Lowered.operand
val read_array_length : t -> Z.t
