type t = Shape of Memory_layout.shape | Storage of Ground.ty | Handle | Shared of Ground.ty | Any

val classify : Memory_layout.env -> Ground.ty -> t
