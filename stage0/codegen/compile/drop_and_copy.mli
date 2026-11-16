type t

val create : Memory_layout.env -> t
val is_trivial : t -> Ground.ty -> bool
val drop : t -> Ground.ty -> Emit_c.Builder.instance
val build_any_drop : t -> Ground.ty -> Emit_c.Builder.instance
val build_any_copy : t -> Ground.ty -> Emit_c.Builder.instance
val copy : t -> Ground.ty -> Emit_c.Builder.instance

val copy_into :
  t -> Emit_c.Builder.t -> destination:Lowered.place -> source:Lowered.place -> Ground.ty -> unit

val allocate_box : t -> Emit_c.Builder.t -> Ground.ty -> Lowered.local
val list_any_entries : Ground.ty -> is_copyable:bool -> (Instance.key * Lowered.signature) list
val compute_first_method_slot : is_copyable:bool -> int

module For_testing : sig
  val copy_signature : t -> Ground.ty -> Lowered.signature
end
