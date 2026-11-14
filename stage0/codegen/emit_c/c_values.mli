type function_context = { symbol : string; local : Lir.local -> string * Lir.ty }

val local_name : Lir.local -> string option -> string
val erased : C_types.context -> Lir.ty -> bool
val declare_prototype : C_types.context -> string -> string -> unit
val bytes_name : C_types.context -> string -> string
val function_ref_symbol : function_context -> Lir.function_ref -> string
val block_pointer : C_types.context -> string -> Ground.ty -> string -> string
val place_c : C_types.context -> function_context -> Lir.place -> (string * Lir.ty) option
val operand_c : C_types.context -> function_context -> Lir.operand -> (string * Lir.ty) option
val constant_c : C_types.context -> Lir.constant -> string * Lir.ty
val scalar_of : C_types.context -> Lir.ty -> Memory_layout.scalar
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
  Lir.signature ->
  string

val rvalue_c : C_types.context -> function_context -> Lir.ty -> Lir.rvalue -> built option
