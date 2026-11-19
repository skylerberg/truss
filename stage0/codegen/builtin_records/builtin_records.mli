module Handle : sig
  val shape : Memory_layout.shape
  val project_descriptor : Lowered.place -> Lowered.place
  val build : descriptor:Lowered.operand -> Lowered.rvalue
end

module Shared : sig
  val shape : Memory_layout.shape
  val project_value : Lowered.place -> Lowered.place
  val build : Ground.ty -> value:Lowered.operand -> Lowered.rvalue
end

module Any : sig
  val shape : Memory_layout.shape
  val project_value : Lowered.place -> Lowered.place
  val project_vtable : Lowered.place -> Lowered.place
  val build : Ground.ty -> value:Lowered.operand -> vtable:Lowered.operand -> Lowered.rvalue
end

module Function_value : sig
  val make_shape : Ground.function_type -> Memory_layout.shape
  val project_code : Lowered.place -> Lowered.place
  val project_environment : Lowered.place -> Lowered.place
  val list_fields : code:'value -> environment:'value -> (string * 'value) list
end
