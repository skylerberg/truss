type t = Shape of Memory_layout.shape | Storage of Ground.ty | Handle | Shared of Ground.ty | Any

let classify env (ty : Ground.ty) =
  match (Storage.match_storage_element ty, ty) with
  | Some element, _ -> Storage element
  | None, Named { path; arguments = [] } when Intrinsic.builtin_of_path path = Some Handle -> Handle
  | None, Named { path; arguments = [ Type value ] }
    when Intrinsic.builtin_of_path path = Some Shared ->
      Shared value
  | None, Any _ -> Any
  | None, _ -> Shape (Memory_layout.shape env ty)
