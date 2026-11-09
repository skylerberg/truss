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

val fork : t -> t
(** A copy that shares every result and diverges from here on: the state a new worktree or a commit
    starts from. *)

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

(** {1 Saving and loading}

    A session's graph is saved as a journal: a base holding every saved node, and a record of the
    changes since then for each save. Values are put in the store by hash. *)

val attach : t -> Store.t -> unit
(** Puts and gets the engine's saved values through the store. *)

val save : t -> Store.journal -> unit
(** Appends what changed since the last save, or writes a new base once the changes outgrow it. *)

val save_all : t -> Store.journal -> unit
(** Writes a new base holding every saved node. *)

val load : ?log:bool -> ?shared:t -> ?frozen:bool -> Store.t -> Store.journal -> t option
(** An engine filled from a journal, or [None] if the journal has nothing; with [~frozen:true], a
    frozen layer. Results are read from the store when first needed. *)

val values_in : Store.journal -> string list
(** Every value a journal refers to, for collecting the store. *)
