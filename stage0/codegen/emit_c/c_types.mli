type key =
  | Type of Ground.ty
  | Block of Ground.ty * string
  | Code of Ground.function_type
  | Environment of string * int
  | Evidence of int
  | Capabilities of int

module Keys : Map.S with type key = key

val render_key_name : key -> string

type definition =
  | Typedef of string
  | Code_typedef of string
  | Struct of { body : string; holds : key list }

type defined = { definition : definition; references : key list }

type t = {
  env : Memory_layout.env;
  mutable order : key list;
  mutable registered : unit Keys.t;
  mutable environments : (string * Lowered.ty) list Keys.t;
  mutable references : key list option;
}

val create : Memory_layout.env -> t
val add_environment : t -> key -> (string * Lowered.ty) list -> unit
val register : t -> Keys.key -> unit
val compute_layout : t -> Ground.ty -> Memory_layout.t
val is_struct : t -> Ground.ty -> bool
val render_value_type : t -> Ground.ty -> string
val render_scalar_type : t -> Memory_layout.scalar -> string
val render_type : t -> string -> Lowered.ty -> string
val render_signature_parameters : t -> string -> Lowered.ty list -> string list option -> string
val define : t -> Keys.key -> defined
