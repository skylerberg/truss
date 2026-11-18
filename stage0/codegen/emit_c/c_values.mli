type function_context = { symbol : string; render_local : Lowered.local -> string * Lowered.ty }

val render_local_name : Lowered.local -> string option -> string
val is_erased : Emission.t -> Lowered.ty -> bool
val render_bytes_definition : string * string -> string
val render_function_ref_symbol : function_context -> Lowered.function_ref -> string
val render_block_pointer : Emission.t -> string -> Ground.ty -> string -> string
val render_place : Emission.t -> function_context -> Lowered.place -> (string * Lowered.ty) option

val render_operand :
  Emission.t -> function_context -> Lowered.operand -> (string * Lowered.ty) option

val render_constant : Emission.t -> Lowered.constant -> string * Lowered.ty
val classify_scalar : Emission.t -> Lowered.ty -> Memory_layout.scalar
val compute_bit_width : Memory_layout.scalar -> int
val render_unsigned_type : Emission.t -> Memory_layout.scalar -> string
val render_niche_value : Emission.t -> Memory_layout.niche -> Z.t -> string
val render_path : string -> Memory_layout.step list -> string
val render_discriminant_test : Emission.t -> string -> Memory_layout.discriminant -> string

type built =
  | Expression of string
  | Allocating of { block : C_types.key; fill : string; value : string -> string }

val render_prototype :
  Emission.t ->
  string ->
  string ->
  ?names:string list ->
  linkage:C_runtime.linkage ->
  Lowered.signature ->
  string

val render_rvalue : Emission.t -> function_context -> Lowered.ty -> Lowered.rvalue -> built option
