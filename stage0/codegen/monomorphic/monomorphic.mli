exception Todo_type of Ground.ty

type context = {
  find_type_interface : Path.t -> Types.type_interface option;
  normalize : Types.ty -> Types.ty;
  normalize_capabilities : Types.capability_set -> Types.capability_set;
}

val ground : context -> Types.substitution -> Types.ty -> Ground.ty
val ground_argument : context -> Types.substitution -> Types.argument -> Ground.argument
val list_capabilities : context -> Types.substitution -> Types.capability_set -> Path.t list
val convert_capability_arguments : Ground.instantiation -> (string * Types.capability_set) list
val make_substitution : Types.generic list -> Ground.argument list -> Types.substitution
val make_signature_substitution : Types.signature -> Ground.instantiation -> Types.substitution

val ground_instantiation :
  context -> Types.substitution -> Types.instantiation -> Ground.instantiation

val find_builtin_shape : Ground.ty -> Memory_layout.shape option
val compute_shape : context -> Ground.ty -> Memory_layout.shape
