val unmarshal : string -> 'a
val forget_fingerprint : Nodes.node -> unit
val fingerprint : Nodes.t -> Nodes.node -> string option
val ensure_stored : ?stores_every_value:bool -> Nodes.t -> Nodes.node -> unit
val key_part : Nodes.t -> Nodes.node -> string option
val stored_bytes : Nodes.t -> Nodes.node -> string option
val input_value : Nodes.t -> ('key, 'value) Nodes.input_cell -> 'value option
val load : Nodes.t -> ('key, 'value) Nodes.result_cell -> 'value Nodes.outcome option

val same_outcomes :
  ('key, 'value) Nodes.query -> 'value Nodes.outcome -> 'value Nodes.outcome -> bool

val current_reads : Nodes.t -> Nodes.node -> Nodes.node list
val fact_key : Nodes.store -> Nodes.node -> (Nodes.node * string) list -> string
val reads_key : Nodes.store -> Nodes.node -> string

type restorer = {
  restore : Nodes.t -> key:string -> Nodes.node;
  locate : Nodes.t -> key:string -> Nodes.node;
  find : Nodes.t -> key:string -> Nodes.node option;
}

val restorers : (string, restorer) Hashtbl.t
