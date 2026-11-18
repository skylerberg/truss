type function_context = { symbol : string; render_local : Lowered.local -> string * Lowered.ty }

val render_local_name : Lowered.local -> string option -> string
val is_erased : C_types.context -> Lowered.ty -> bool
val declare_prototype : C_types.context -> string -> string -> unit
val render_site : C_types.context -> Lowered.site -> string
val render_bytes_symbol : C_types.context -> int -> string
val render_bytes_name : C_types.context -> string -> string
val render_bytes_definition : string * string -> string
val render_function_ref_symbol : function_context -> Lowered.function_ref -> string
val render_block_pointer : C_types.context -> string -> Ground.ty -> string -> string

val render_place :
  C_types.context -> function_context -> Lowered.place -> (string * Lowered.ty) option

val render_operand :
  C_types.context -> function_context -> Lowered.operand -> (string * Lowered.ty) option

val render_constant : C_types.context -> Lowered.constant -> string * Lowered.ty
val classify_scalar : C_types.context -> Lowered.ty -> Memory_layout.scalar
val compute_bit_width : Memory_layout.scalar -> int
val render_unsigned_type : C_types.context -> Memory_layout.scalar -> string
val render_niche_value : C_types.context -> Memory_layout.niche -> Z.t -> string
val render_path : string -> Memory_layout.step list -> string
val render_discriminant_test : C_types.context -> string -> Memory_layout.discriminant -> string

type built =
  | Expression of string
  | Allocating of { block : C_types.key; fill : string; value : string -> string }

val render_prototype :
  C_types.context ->
  string ->
  string ->
  ?names:string list ->
  linkage:C_runtime.linkage ->
  Lowered.signature ->
  string

val render_rvalue :
  C_types.context -> function_context -> Lowered.ty -> Lowered.rvalue -> built option
