type function_context = { symbol : string; local : Lowered.local -> string * Lowered.ty }

val local_name : Lowered.local -> string option -> string
val erased : C_types.context -> Lowered.ty -> bool
val declare_prototype : C_types.context -> string -> string -> unit
val bytes_name : C_types.context -> string -> string
val function_ref_symbol : function_context -> Lowered.function_ref -> string
val block_pointer : C_types.context -> string -> Ground.ty -> string -> string
val place_c : C_types.context -> function_context -> Lowered.place -> (string * Lowered.ty) option

val operand_c :
  C_types.context -> function_context -> Lowered.operand -> (string * Lowered.ty) option

val constant_c : C_types.context -> Lowered.constant -> string * Lowered.ty
val scalar_of : C_types.context -> Lowered.ty -> Memory_layout.scalar
val bit_width : C_types.context -> Memory_layout.scalar -> int
val unsigned_of : C_types.context -> Memory_layout.scalar -> string
val niche_value : C_types.context -> Memory_layout.niche -> Z.t -> string
val is_variant_c : C_types.context -> string -> Ground.ty -> string -> string

type built =
  | Expression of string
  | Allocating of { block : C_types.key; fill : string; value : string -> string }

val prototype :
  C_types.context ->
  string ->
  string ->
  ?names:string list ->
  linkage:C_runtime.linkage ->
  Lowered.signature ->
  string

val rvalue_c : C_types.context -> function_context -> Lowered.ty -> Lowered.rvalue -> built option
