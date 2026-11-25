type t =
  | Shape of Memory_layout.shape
  | Storage of Ground.ty
  | View of Ground.ty
  | Handle
  | Shared of Ground.ty

let classify env (ty : Ground.ty) =
  match ty with
  | Named { path; arguments } -> (
      match (Well_known.find_builtin_type path, arguments) with
      | Some Storage, [ Type element ] -> Storage element
      | Some View, [ Type viewed ] -> View viewed
      | Some Handle, [] -> Handle
      | Some Shared, [ Type value ] -> Shared value
      | _ -> Shape (Memory_layout.compute_shape env ty))
  | Function _ | Never -> Shape (Memory_layout.compute_shape env ty)
