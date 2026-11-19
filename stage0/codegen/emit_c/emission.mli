type t = {
  types : C_types.t;
  item : Lowered.Item.t;
  bytes : (string, int) Hashtbl.t;
  mutable references : Lowered.Item.t list;
  mutable sites : Lowered.site list;
  mutable capabilities : Path.t list;
  mutable prototypes : (C_text.t * C_text.t) list;
  mutable statics : C_text.t list;
  mutable helpers_used : C_runtime.helper list;
  mutable called : Lowered.Item.t list;
  mutable calls : (Path.t * int) list;
  mutable failures : (C_runtime.failure * Lowered.site) list;
}

val create : Memory_layout.env -> item:Lowered.Item.t -> t
val render_item : t -> Lowered.Item.t -> C_text.t
val render_called_item : t -> Lowered.Item.t -> C_text.t
val render_site : t -> Lowered.site -> C_text.t
val render_capability : t -> Path.t -> C_text.t
val record_capability_call : t -> capability:Path.t -> slot:int -> unit
val record_failure : t -> C_runtime.failure -> Lowered.site -> unit
val declare_prototype : t -> C_text.t -> C_text.t -> unit
val render_bytes_name : t -> string -> C_text.t
val use_helper : t -> C_runtime.helper -> C_text.t
val add_static : t -> (C_text.t -> C_text.t) -> C_text.t
val list_references : t -> Lowered.Item.t list
val list_bytes : t -> (int * string) list
