type debug_form = Structure | Text | Sequence
type t

val create :
  Memory_layout.env ->
  representation:(Ground.ty -> Memory_layout.representation) ->
  uint64:Ground.ty ->
  ?debug_form:(Ground.ty -> debug_form) ->
  unit ->
  t

val trivial : t -> Ground.ty -> bool
val drop : t -> Ground.ty -> Emit_c.Builder.instance
val copy : t -> Ground.ty -> Emit_c.Builder.instance
val any_drop : t -> Ground.ty -> Emit_c.Builder.instance
val output_ty : Ground.ty
val encode : t -> Ground.ty -> Emit_c.Builder.instance

val encode_call :
  t -> Emit_c.Builder.t -> output:Lowered.operand -> Ground.ty -> Lowered.place -> unit

val copy_into :
  t -> Emit_c.Builder.t -> destination:Lowered.place -> source:Lowered.place -> Ground.ty -> unit

val debug : t -> Ground.ty -> Emit_c.Builder.instance
val debug_signature : t -> Ground.ty -> Lowered.signature

module For_testing : sig
  val copy_signature : t -> Ground.ty -> Lowered.signature
end
