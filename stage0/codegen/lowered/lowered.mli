include module type of struct
  include Lowered_types
end

val local_place : local -> place
val project : place -> projection -> place

val projection_type :
  Memory_layout.env -> environment:(int -> (string * ty) list) -> ty -> projection -> ty option

val successors : terminator -> block list
val erased : Memory_layout.env -> ty -> bool
