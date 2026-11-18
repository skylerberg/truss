type t = {
  types : C_types.t;
  prefix : string;
  bytes : (string, int) Hashtbl.t;
  mutable prototypes : (string * string) list;
  mutable sites : Lowered.site list;
  mutable statics : string list;
  mutable referenced_items : Lowered.Item.t list;
  mutable called : Lowered.Item.t list;
  mutable calls : (Path.t * int) list;
  mutable failures : (C_runtime.failure * Lowered.site) list;
}

val create : Memory_layout.env -> prefix:string -> t
val refer : t -> Lowered.Item.t -> unit
val record_call : t -> Lowered.Item.t -> unit
val record_capability_call : t -> capability:Path.t -> slot:int -> unit
val record_failure : t -> C_runtime.failure -> Lowered.site -> unit
val list_referenced_items : t -> referrer:Lowered.Item.t -> Lowered.Item.t list
val declare_prototype : t -> string -> string -> unit
val render_site : t -> Lowered.site -> string
val render_bytes_symbol : t -> int -> string
val render_bytes_name : t -> string -> string
val add_static : t -> (string -> string) -> string
