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

type context = {
  env : Memory_layout.env;
  prefix : string;
  mutable order : key list;
  mutable registered : unit Keys.t;
  mutable environments : (string * Lowered.ty) list Keys.t;
  bytes : (string, int) Hashtbl.t;
  mutable prototypes : (string * string) list;
  mutable sites : Lowered.site list;
  mutable references : key list option;
  mutable helpers_used : string list;
  mutable statics : string list;
  mutable referenced_items : Lowered.Item.t list;
  mutable called : Lowered.Item.t list;
  mutable calls : (Path.t * int) list;
  mutable failures : (C_runtime.failure * Lowered.site) list;
}

val make_context : Memory_layout.env -> string -> context
val refer : context -> Lowered.Item.t -> unit
val list_referenced_items : context -> referrer:Lowered.Item.t -> Lowered.Item.t list
val use_helper : context -> string -> string
val register : context -> Keys.key -> unit
val compute_layout : context -> Ground.ty -> Memory_layout.t
val is_struct : context -> Ground.ty -> bool
val render_value_type : context -> Ground.ty -> string
val render_scalar_type : context -> Memory_layout.scalar -> string
val render_type : context -> string -> Lowered.ty -> string

val render_signature_parameters :
  context -> string -> Lowered.ty list -> string list option -> string

val define : context -> Keys.key -> defined
