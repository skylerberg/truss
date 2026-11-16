exception Todo_type of Ground.ty

type context = {
  type_interface : Path.t -> Types.type_interface option;
  normalize : Types.ty -> Types.ty;
  normalize_capabilities : Types.capability_set -> Types.capability_set;
}

val ground : context -> Types.substitution -> Types.ty -> Ground.ty
val ground_argument : context -> Types.substitution -> Types.argument -> Ground.argument
val ground_mode : Types.mode -> Ground.mode
val list_evidence : context -> Types.substitution -> Types.capability_set -> Path.t list
val make_substitution : Types.generic list -> Ground.argument list -> Types.substitution
val panic_capability : Path.t
val compute_shape : context -> Ground.ty -> Memory_layout.shape
