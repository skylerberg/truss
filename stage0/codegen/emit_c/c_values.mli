type function_context = Lowered.local -> C_text.t * Lowered.ty

val render_cast : C_text.t -> C_text.t -> C_text.t
val render_local_name : Lowered.local -> string option -> string
val render_bytes_initializer : string -> string
val render_block_pointer : Emission.t -> C_text.t -> Ground.ty -> string -> C_text.t
val render_place : Emission.t -> function_context -> Lowered.place -> (C_text.t * Lowered.ty) option

val render_operand :
  Emission.t -> function_context -> Lowered.operand -> (C_text.t * Lowered.ty) option

val render_constant : Emission.t -> Lowered.constant -> C_text.t * Lowered.ty
val render_comparison : Emission.t -> function_context -> Lowered.test -> C_text.t
val classify_scalar : Emission.t -> Lowered.ty -> Memory_layout.scalar
val compute_bit_width : Memory_layout.scalar -> int
val render_unsigned_type : Emission.t -> Memory_layout.scalar -> C_text.t
val render_niche_value : Emission.t -> Memory_layout.niche -> Z.t -> C_text.t
val render_path : Memory_layout.step list -> string
val render_discriminant_test : Emission.t -> C_text.t -> Memory_layout.discriminant -> C_text.t

type built =
  | Expression of C_text.t
  | Allocating of { block : C_text.key; fill : C_text.t; value : C_text.t -> C_text.t }

val render_prototype :
  Emission.t ->
  C_text.t ->
  ?names:C_text.t list ->
  linkage:C_runtime.linkage ->
  Lowered.signature ->
  C_text.t

val render_initializer : Emission.t -> Ground.ty -> Lowered.static_value -> C_text.t option
val render_rvalue : Emission.t -> function_context -> Lowered.ty -> Lowered.rvalue -> built option
