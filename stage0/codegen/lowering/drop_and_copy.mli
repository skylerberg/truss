type t

val create : Memory_layout.env -> t
val is_trivial : t -> Ground.ty -> bool
val drop : t -> Ground.ty -> Emit_c.fragment
val build_untyped_drop : t -> Ground.ty -> Emit_c.fragment
val copy : t -> Ground.ty -> Emit_c.fragment

val copy_into :
  t -> Emit_c.Ir_builder.t -> destination:Lowered.place -> source:Lowered.place -> Ground.ty -> unit

module For_testing : sig
  val copy_signature : t -> Ground.ty -> Lowered.signature
end
