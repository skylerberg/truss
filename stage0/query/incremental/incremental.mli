exception Cycle of string list
exception Lost of string

type part = Tree | Resolved | Interface | Shape | Signature | Body | Ownership
type subject = { path : Path.t; part : part }

val show_part : part -> string

type t
type context
type node
type ('key, 'value) input
type ('key, 'value) query

val input :
  name:string ->
  show:('key -> string) ->
  ?equal:('value -> 'value -> bool) ->
  ?about:('key -> subject option) ->
  unit ->
  ('key, 'value) input

val query :
  name:string ->
  show:('key -> string) ->
  phase:int ->
  ?saved:bool ->
  ?portable:bool ->
  ?equal:('value -> 'value -> bool) ->
  ?about:('key -> subject option) ->
  (context -> 'key -> 'value) ->
  ('key, 'value) query

val seal : unit -> unit
val phases : int
val read : context -> ('key, 'value) input -> 'key -> 'value option
val demand : context -> ('key, 'value) query -> 'key -> 'value
val create : ?log:bool -> ?bases:t list -> unit -> t
val freeze : ?fixed:bool -> t -> unit
val context : t -> context
val observer : t -> context
val engine_of : context -> t
val set : t -> ('key, 'value) input -> 'key -> 'value -> unit
val remove : t -> ('key, 'value) input -> 'key -> unit

type change = { computed : node list; changed : node list }

val stabilize : t -> change
val unroot : t -> ('key, 'value) query -> 'key -> unit
val executed : t -> string list
val computed : t -> ('key, 'value) query -> 'key list
val result_label : ('key, 'value) query -> 'key -> string
val clear_log : t -> unit

type counters = {
  marked : int;
  confirmed : int;
  computed : int;
  changed : int;
  adopted : int;
  copied : int;
  collected : int;
}

val counters : t -> counters
val label : node -> string
val subject : node -> subject option
val is_input : node -> bool
val nodes : t -> node list
val nodes_including_fixed : t -> node list
val count : t -> int
val is_fixed : node -> bool
val reads : t -> node -> node list
val readers : t -> node -> node list
val differing : t -> node list
val unshared : t -> t -> node list
val identity : node -> string
val current_in : node -> t -> node option
val same_outcome : t -> node -> t -> node -> bool

type store = {
  id : string;
  version : string;
  put : string -> string;
  get : string -> string option;
  find_fact : string -> string option;
  add_fact : string -> string -> unit;
  find_reads : string -> string option;
  add_reads : string -> string -> unit;
}

val attach : t -> store -> unit
val record_facts : t -> unit
val write : ?full:bool -> ?stores_every_value:bool -> t -> string

type chain_size = { whole : int; differences : int; depth : int }

val chain_size : t -> chain_size
val unwritten : t -> bool
val artifact : t -> string option
val open_ : ?log:bool -> store -> bases:t list -> string -> t option
val frozen_of : store -> bases:t list -> fixed:bool -> string -> t option
val inputs_stored : t -> bool
val values_in : store -> string -> string list
val forget_bases : unit -> unit
val audit : ?include_bases:bool -> ?before:int -> t -> string list
val auditing : bool ref
val audit_all : unit -> string list
val skip_audit : t -> unit
