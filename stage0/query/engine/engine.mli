type t = Incremental.t

val seal : unit -> unit
val create : ?log:bool -> ?bases:t list -> unit -> t
val freeze : ?fixed:bool -> t -> unit
val context : t -> Query.context
val observer : t -> Query.context
val of_context : Query.context -> t
val set : t -> ('key, 'value) Query.input -> 'key -> 'value -> unit
val remove : t -> ('key, 'value) Query.input -> 'key -> unit
val get : t -> ('key, 'value) Query.query -> 'key -> 'value
val unroot : t -> ('key, 'value) Query.query -> 'key -> unit

type node = Incremental.node
type change = Incremental.change = { computed : node list; changed : node list }

val stabilize : t -> change

type counters = Incremental.counters = {
  marked : int;
  confirmed : int;
  computed : int;
  changed : int;
  adopted : int;
  copied : int;
  collected : int;
}

val counters : t -> counters
val nodes : t -> node list
val nodes_including_fixed : t -> node list
val is_input : node -> bool
val readers : t -> node -> node list
val unshared : t -> t -> node list
val identity : node -> string
val label : node -> string
val subject : node -> Query.subject option
val is_fixed : node -> bool
val reads : t -> node -> node list
val current_in : node -> t -> node option
val same_outcome : t -> node -> t -> node -> bool
val attach : t -> Store.t -> version:string -> unit
val record_facts : t -> unit
val write : ?full:bool -> ?stores_every_value:bool -> t -> string

type chain_size = Incremental.chain_size = { whole : int; differences : int; depth : int }

val chain_size : t -> chain_size
val unwritten : t -> bool
val artifact : t -> string option
val open_base : Store.t -> version:string -> bases:t list -> string -> t option
val open_ : ?log:bool -> Store.t -> version:string -> bases:t list -> string -> t option

exception Lost of string

val inputs_stored : t -> bool
val values_in : Store.t -> version:string -> string -> string list
val forget_bases : unit -> unit
val audit : ?include_bases:bool -> ?before:Query.phase -> t -> string list
val skip_audit : t -> unit

module For_testing : sig
  val executed : t -> string list
  val computed : t -> ('key, 'value) Query.query -> 'key list
  val result_label : ('key, 'value) Query.query -> 'key -> string
  val clear_log : t -> unit
  val differing : t -> node list
  val count : t -> int
  val audit_all : unit -> string list
  val auditing : bool ref
end
