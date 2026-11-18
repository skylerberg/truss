let by_value_limit = 16

let rec holds_elements (layout : Memory_layout.t) =
  layout.size > 0
  &&
  match layout.form with
  | Array _ -> true
  | Struct fields ->
      List.exists (fun (field : Memory_layout.field) -> holds_elements field.layout) fields
  | Tagged { variants; _ } ->
      List.exists (fun (variant : Memory_layout.variant) -> holds_elements variant.payload) variants
  | Niche_encoded { dataful; _ } -> holds_elements dataful.payload
  | Zero_size | Scalar _ | Tag_only _ -> false

let classify_parameter env (mode : Ground.mode) ty =
  let layout = Memory_layout.of_type env ty in
  if layout.size = 0 then None
  else
    let small = layout.size <= by_value_limit in
    Some
      (match mode with
      | Read ->
          if small && not (holds_elements layout) then Lowered.Value ty
          else Pointer { target = Value ty; writable = false }
      | Mut -> Pointer { target = Value ty; writable = true }
      | Own -> if small then Value ty else Pointer { target = Value ty; writable = true })

type result = Nothing | Returned of Lowered.ty | Through_pointer of Lowered.ty

let classify_result env (ty : Ground.ty) =
  match ty with
  | Never -> Nothing
  | _ ->
      let layout = Memory_layout.of_type env ty in
      if layout.size = 0 then Nothing
      else if layout.size <= by_value_limit then Returned (Value ty)
      else Through_pointer (Pointer { target = Value ty; writable = true })

let make_signature ?(returns = true) parameters result : Lowered.signature =
  match result with
  | Nothing -> { parameters; result = None; returns }
  | Returned ty -> { parameters; result = Some ty; returns }
  | Through_pointer pointer -> { parameters = pointer :: parameters; result = None; returns }

let make_destination result place : Lowered.destination =
  match result with Through_pointer _ -> Written place | Returned _ | Nothing -> Returned place

let evidence = Lowered.Raw (Pointer Opaque)
let capabilities = Lowered.Raw (Nullable_pointer Opaque)

let make_function_value_signature env (function_type : Ground.function_type) : Lowered.signature =
  let result_ty, returns =
    match function_type.result with
    | Never -> (Nothing, false)
    | ty -> (classify_result env ty, true)
  in
  let written =
    List.filter_map (fun (mode, ty) -> classify_parameter env mode ty) function_type.parameters
  in
  let environment = Lowered.Raw (Nullable_pointer Opaque) in
  let signature = make_signature ~returns (written @ [ capabilities ]) result_ty in
  { signature with parameters = environment :: signature.parameters }

let make_function_value_shape function_type : Memory_layout.shape =
  Record
    [ ("code", Raw (Pointer (Code function_type))); ("environment", Raw (Nullable_pointer Opaque)) ]

let drop_signature ty : Lowered.signature =
  { parameters = [ Pointer { target = Value ty; writable = true } ]; result = None; returns = true }
