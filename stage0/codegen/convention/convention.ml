let by_value_limit = 16

let parameter env (mode : Ground.mode) ty =
  let layout = Memory_layout.of_type env ty in
  if layout.size = 0 then None
  else
    let small = layout.size <= by_value_limit in
    Some
      (match mode with
      | Read -> if small then Lir.Value ty else Pointer { target = Value ty; writable = false }
      | Mut -> Pointer { target = Value ty; writable = true }
      | Own -> if small then Value ty else Pointer { target = Value ty; writable = true })

type result = Nothing | Returned of Lir.ty | Through_pointer of Lir.ty

let result env (ty : Ground.ty) =
  match ty with
  | Never -> Nothing
  | _ ->
      let layout = Memory_layout.of_type env ty in
      if layout.size = 0 then Nothing
      else if layout.size <= by_value_limit then Returned (Value ty)
      else Through_pointer (Pointer { target = Value ty; writable = true })

let signature ?(returns = true) parameters result : Lir.signature =
  match result with
  | Nothing -> { parameters; result = None; returns }
  | Returned ty -> { parameters; result = Some ty; returns }
  | Through_pointer pointer -> { parameters = pointer :: parameters; result = None; returns }

let destination result place : Lir.destination =
  match result with Through_pointer _ -> Written place | Returned _ | Nothing -> Returned place

let evidence = Lir.Raw (Pointer Opaque)

let function_value env (f : Ground.function_type) : Lir.signature =
  let result_ty, returns =
    match f.result with
    | Returns Never -> (Nothing, false)
    | Returns ty -> (result env ty, true)
    | Yields _ | Lends _ -> invalid_arg "Convention.function_value: a function type that yields"
  in
  let written = List.filter_map (fun (mode, ty) -> parameter env mode ty) f.parameters in
  let evidence = List.map (fun _ -> evidence) f.uses in
  let environment = Lir.Raw (Nullable_pointer Opaque) in
  let signature = signature ~returns (written @ evidence) result_ty in
  { signature with parameters = environment :: signature.parameters }

let function_value_shape f : Memory_layout.shape =
  Record [ ("code", Raw (Pointer (Code f))); ("environment", Raw (Nullable_pointer Opaque)) ]

let drop_signature ty : Lir.signature =
  { parameters = [ Pointer { target = Value ty; writable = true } ]; result = None; returns = true }
