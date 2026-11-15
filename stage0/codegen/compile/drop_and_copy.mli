type t

val create : Memory_layout.env -> t
val is_trivial : t -> Ground.ty -> bool
val drop : t -> Ground.ty -> Emit_c.Builder.instance
val any_drop : t -> Ground.ty -> Emit_c.Builder.instance
val any_copy : t -> Ground.ty -> Emit_c.Builder.instance
val copy : t -> Ground.ty -> Emit_c.Builder.instance

val copy_into :
  t -> Emit_c.Builder.t -> destination:Lowered.place -> source:Lowered.place -> Ground.ty -> unit

val box : t -> Emit_c.Builder.t -> Ground.ty -> Lowered.local

type any_operation = Drop_operation | Copy_operation

val lay_out_any_operations : is_copyable:bool -> any_operation list
val make_any_entry : any_operation -> Ground.ty -> Instance.key * Lowered.signature
val free_box : Emit_c.Builder.t -> Lowered.place -> unit

module For_testing : sig
  val copy_signature : t -> Ground.ty -> Lowered.signature
end
