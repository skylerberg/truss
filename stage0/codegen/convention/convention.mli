val classify_parameter : Memory_layout.env -> Language.Mode.t -> Ground.ty -> Lowered.ty option

type result = Nothing | Returned of Lowered.ty | Through_pointer of Lowered.ty

val classify_result : Memory_layout.env -> Ground.ty -> result
val make_signature : ?returns:bool -> Lowered.ty list -> result -> Lowered.signature
val make_destination : result -> Lowered.place -> Lowered.destination
val make_function_value_signature : Memory_layout.env -> Ground.function_type -> Lowered.signature
val drop_signature : Ground.ty -> Lowered.signature
val evidence : Lowered.ty
val capabilities : Lowered.ty
