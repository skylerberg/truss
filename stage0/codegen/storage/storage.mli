val make_storage_type : Ground.ty -> Ground.ty
val find_storage_element : Ground.ty -> Ground.ty option
val make_storage_shape : Ground.ty -> Memory_layout.shape
val empty_buffer : Lowered.constant
val project_buffer : Lowered.place -> Lowered.place
val project_length : Lowered.place -> Lowered.place
val project_capacity : Lowered.place -> Lowered.place
val index_element : Lowered.place -> Lowered.operand -> Lowered.place
val make_owned_block_test : Lowered.place -> Lowered.test

val build_storage :
  Ground.ty ->
  buffer:Lowered.operand ->
  length:Lowered.operand ->
  capacity:Lowered.operand ->
  Lowered.rvalue

val list_storage_fields :
  buffer:'value -> length:'value -> capacity:'value -> (string * 'value) list

val build_borrowed : Ground.ty -> buffer:Lowered.operand -> length:Lowered.operand -> Lowered.rvalue
val build_empty : Ground.ty -> Lowered.rvalue
