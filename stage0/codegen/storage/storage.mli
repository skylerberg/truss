val make_storage_type : Ground.ty -> Ground.ty
val make_view_type : Ground.ty -> Ground.ty
val match_storage_element : Ground.ty -> Ground.ty option
val match_view_element : Ground.ty -> Ground.ty option
val make_storage_shape : uint64:Ground.ty -> Ground.ty -> Memory_layout.shape
val make_view_shape : uint64:Ground.ty -> Ground.ty -> Memory_layout.shape
val buffer_field : string
val length_field : string
val capacity_field : string
val project_buffer : Lowered.place -> Lowered.place
val project_length : Lowered.place -> Lowered.place
val project_capacity : Lowered.place -> Lowered.place
val index_element : Lowered.place -> Lowered.operand -> Lowered.place
val project_view_elements : Lowered.place -> Lowered.place
val project_view_length : Lowered.place -> Lowered.place
val index_view_element : Lowered.place -> Lowered.operand -> Lowered.place
val build_is_allocated : Lowered.place -> Lowered.rvalue

val build_storage :
  Ground.ty ->
  buffer:Lowered.operand ->
  length:Lowered.operand ->
  capacity:Lowered.operand ->
  Lowered.rvalue

val build_empty : Ground.ty -> Lowered.rvalue
val build_view : Ground.ty -> elements:Lowered.operand -> length:Lowered.operand -> Lowered.rvalue
