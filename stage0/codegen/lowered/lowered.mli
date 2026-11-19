module Item = Item

include module type of struct
  include Lowered_types
end

val make_local_place : local -> place
val project : place -> projection -> place
val make_uint64_constant : int -> operand

val find_projection_type :
  Memory_layout.env -> list_environment:(int -> (string * ty) list) -> ty -> projection -> ty option

val list_successors : terminator -> block list
val is_erased : Memory_layout.env -> ty -> bool
