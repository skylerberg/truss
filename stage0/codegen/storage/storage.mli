val of_elements : Ground.ty -> Ground.ty
val view_of_elements : Ground.ty -> Ground.ty
val elements_of : Ground.ty -> Ground.ty option
val viewed : Ground.ty -> Ground.ty option
val shape : uint64:Ground.ty -> Ground.ty -> Memory_layout.shape
val view_shape : uint64:Ground.ty -> Ground.ty -> Memory_layout.shape
val buffer_field : string
val length_field : string
val capacity_field : string
val buffer : Lowered.place -> Lowered.place
val length : Lowered.place -> Lowered.place
val capacity : Lowered.place -> Lowered.place
val at : Lowered.place -> Lowered.operand -> Lowered.place
val view_elements : Lowered.place -> Lowered.place
val view_length : Lowered.place -> Lowered.place
val view_at : Lowered.place -> Lowered.operand -> Lowered.place
val empty : Ground.ty -> Lowered.rvalue
val static : Ground.ty -> elements:Lowered.operand -> length:Lowered.operand -> Lowered.rvalue

val owning :
  Ground.ty ->
  buffer:Lowered.operand ->
  length:Lowered.operand ->
  capacity:Lowered.operand ->
  Lowered.rvalue

val view : Ground.ty -> elements:Lowered.operand -> length:Lowered.operand -> Lowered.rvalue
