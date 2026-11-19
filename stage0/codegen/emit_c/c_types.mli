module Keys : Map.S with type key = C_text.key

type 'text definition =
  | Typedef of 'text
  | Code_typedef of 'text
  | Struct of { body : 'text; holds : C_text.key list }

type 'text defined = { definition : 'text definition; references : C_text.key list }

val map_defined : ('text -> 'rendered) -> 'text defined -> 'rendered defined

type registry
type t = { env : Memory_layout.env; registry : registry }

val create : Memory_layout.env -> owner:Lowered.Item.t option -> t
val add_environment : t -> int -> (string * Lowered.ty) list -> unit
val read_environment : t -> int -> (string * Lowered.ty) list
val register : t -> C_text.key -> unit
val list_keys : t -> C_text.key list
val render_key : t -> C_text.key -> C_text.t
val compute_layout : t -> Ground.ty -> Memory_layout.t
val is_struct : t -> Ground.ty -> bool
val render_value_type : t -> Ground.ty -> C_text.t
val render_scalar_type : t -> Memory_layout.scalar -> C_text.t
val render_type : t -> Lowered.ty -> C_text.t
val render_signature_parameters : t -> Lowered.ty list -> C_text.t list option -> C_text.t
val define : t -> C_text.key -> C_text.t defined
