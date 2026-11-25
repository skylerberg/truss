type t =
  | Shape of Memory_layout.shape
  | Storage of Ground.ty
  | View of Ground.ty
  | Handle
  | Shared of Ground.ty

val classify : Memory_layout.env -> Ground.ty -> t
