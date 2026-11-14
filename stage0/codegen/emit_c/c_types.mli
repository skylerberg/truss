type key =
  | Type of Ground.ty
  | Block of Ground.ty * string
  | Code of Ground.function_type
  | Environment of string * int
  | Evidence of int

module Keys : Map.S with type key = key

val key_name : key -> string

type definition =
  | Typedef of string
  | Code_typedef of string
  | Struct of { body : string; holds : key list }

type defined = { definition : definition; references : key list }

type context = {
  env : Memory_layout.env;
  prefix : string;
  mutable order : key list;
  mutable registered : unit Keys.t;
  mutable environments : (string * Lir.ty) list Keys.t;
  mutable bytes : (string * string) list;
  mutable prototypes : (string * string) list;
  mutable anchors : (string * Path.t) list;
  mutable references : key list option;
  mutable helpers_used : string list;
  mutable statics : string list;
  mutable instances : Instance.key list;
  mutable called : Instance.key list;
  mutable calls : (Path.t * int) list;
  mutable failures : (C_runtime.failure * C_runtime.site) list;
  mutable cursors : (Ground.yielding * (string * Lir.ty) list ref) list;
}

val new_context : Memory_layout.env -> string -> context
val refer : context -> Instance.key -> unit
val use_helper : context -> string -> string
val register : context -> Keys.key -> unit
val layout : context -> Ground.ty -> Memory_layout.t
val is_struct : context -> Ground.ty -> bool
val value_c : context -> Ground.ty -> string
val scalar_c : context -> Memory_layout.scalar -> string
val c_ty : context -> string -> Lir.ty -> string
val signature_parameters : context -> string -> Lir.ty list -> string list option -> string
val define : context -> Keys.key -> defined
