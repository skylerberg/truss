let build_record ty fields : Lowered.rvalue = Build { ty; variant = None; fields }

module Handle = struct
  let descriptor_field = "descriptor"
  let shape : Memory_layout.shape = Record [ (descriptor_field, Raw (Integer Int32)) ]
  let project_descriptor handle = Lowered.project handle (Field descriptor_field)

  let build ~descriptor =
    build_record (Ground.make_builtin Handle) [ (descriptor_field, descriptor) ]
end

module Shared = struct
  let value_field = "value"
  let shape : Memory_layout.shape = Record [ (value_field, Raw (Pointer Opaque)) ]
  let project_value shared = Lowered.project shared (Field value_field)

  let build element ~value =
    build_record (Ground.make_builtin Shared ~arguments:[ Type element ]) [ (value_field, value) ]
end

module Any = struct
  let value_field = "value"
  let vtable_field = "vtable"

  let shape : Memory_layout.shape =
    Record [ (value_field, Raw (Pointer Opaque)); (vtable_field, Raw (Pointer Opaque)) ]

  let project_value any = Lowered.project any (Field value_field)
  let project_vtable any = Lowered.project any (Field vtable_field)
  let build ty ~value ~vtable = build_record ty [ (value_field, value); (vtable_field, vtable) ]
end

module Function_value = struct
  let code_field = "code"
  let environment_field = "environment"

  let make_shape function_type : Memory_layout.shape =
    Record
      [
        (code_field, Raw (Pointer (Code function_type)));
        (environment_field, Raw (Nullable_pointer Opaque));
      ]

  let project_code function_value = Lowered.project function_value (Field code_field)
  let project_environment function_value = Lowered.project function_value (Field environment_field)
  let list_fields ~code ~environment = [ (code_field, code); (environment_field, environment) ]
end
