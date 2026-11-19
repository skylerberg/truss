type t

val create : Memory_layout.env -> t
val is_trivial : t -> Ground.ty -> bool
val drop : t -> Ground.ty -> Emit_c.fragment
val build_any_drop : t -> Ground.ty -> Emit_c.fragment
val build_any_copy : t -> Ground.ty -> Emit_c.fragment
val copy : t -> Ground.ty -> Emit_c.fragment

val copy_into :
  t -> Emit_c.Ir_builder.t -> destination:Lowered.place -> source:Lowered.place -> Ground.ty -> unit

val allocate_box : t -> Emit_c.Ir_builder.t -> Ground.ty -> Lowered.local
val list_any_entries : Ground.ty -> is_copyable:bool -> (Lowered.Item.t * Lowered.signature) list
val compute_first_method_slot : is_copyable:bool -> int

module For_testing : sig
  val copy_signature : t -> Ground.ty -> Lowered.signature
end
