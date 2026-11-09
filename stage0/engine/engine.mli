(** What the database sees of the engine: setting inputs, keeping results current, saving and
    loading the graph, and walking it. See DATABASE.md, "The interfaces". Only the database and
    tests use this; compiler stages see {!Query}. *)

type t = Incremental.t

val create : ?log:bool -> ?shared:t -> unit -> t
(** A session's engine, sharing a frozen layer's inputs and results if given. *)

val frozen_layer : ?log:bool -> unit -> t
(** A layer whose inputs are set once, such as the standard library's, which sessions share. *)

val context : t -> Query.context
(** For reads made outside any query. Every result read through it is kept current. *)

val of_context : Query.context -> t
val set : t -> ('key, 'value) Query.input -> 'key -> 'value -> unit
val remove : t -> ('key, 'value) Query.input -> 'key -> unit

val get : t -> ('key, 'value) Query.query -> 'key -> 'value
(** A query's result, computed if needed, and kept current from then on. *)

val release : t -> ('key, 'value) Query.query -> 'key -> unit

type node = Incremental.node
type change = Incremental.change = { computed : node list; changed : node list }

val stabilize : t -> change
(** Brings every kept result up to date, and returns what was computed again since the last
    stabilization, and what came out different. *)

val executed : t -> string list
val clear_log : t -> unit

(** {1 The graph} *)

val nodes : t -> node list
val label : node -> string
val subject : node -> Query.subject option
val reads : node -> node list
val readers : node -> node list
val counterpart : node -> t -> node option
val same_outcome : node -> node -> bool
