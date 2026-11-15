val parameter : Memory_layout.env -> Ground.mode -> Ground.ty -> Lowered.ty option

type result = Nothing | Returned of Lowered.ty | Through_pointer of Lowered.ty

val result : Memory_layout.env -> Ground.ty -> result
val signature : ?returns:bool -> Lowered.ty list -> result -> Lowered.signature
val destination : result -> Lowered.place -> Lowered.destination
val function_value : Memory_layout.env -> Ground.function_type -> Lowered.signature
val function_value_shape : Ground.function_type -> Memory_layout.shape
val drop_signature : Ground.ty -> Lowered.signature
val evidence : Lowered.ty
