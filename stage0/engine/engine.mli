(** What the database sees of the engine: setting inputs, keeping results current, walking the
    graph, and keeping states and facts in the store. Only the database and tests use this; compiler
    stages see {!Query}. *)

type t = Incremental.t
(** One state: what differs from its bases, with the rest read from them. *)

val create : ?log:bool -> ?bases:t list -> unit -> t
(** An engine over frozen bases. *)

val freeze : ?fixed:bool -> t -> unit
(** Brings an engine up to date and makes it a base, which never changes again. A [fixed] base is a
    package's whose sources never change, such as the standard library's. *)

val is_frozen : t -> bool

val context : t -> Query.context
(** For reads made outside any query. Every result read through it is kept. *)

val of_context : Query.context -> t
val set : t -> ('key, 'value) Query.input -> 'key -> 'value -> unit
val remove : t -> ('key, 'value) Query.input -> 'key -> unit

val get : t -> ('key, 'value) Query.query -> 'key -> 'value
(** A query's result, computed if needed, and kept from then on. *)

val release : t -> ('key, 'value) Query.query -> 'key -> unit

type node = Incremental.node
type change = Incremental.change = { computed : node list; changed : node list }

val stabilize : t -> change
(** Brings every result the engine holds up to date, and returns what was computed since the last
    call, and what came out different. *)

val executed : t -> string list
val clear_log : t -> unit

type counters = Incremental.counters = {
  marked : int;
  confirmed : int;
  computed : int;
  changed : int;
  adopted : int;
  copied : int;
  dropped : int;
}

val counters : t -> counters
(** The work an engine has done since it was made. *)

(** {1 The graph} *)

val nodes : t -> node list
(** Every input and result of the state, apart from its fixed bases'. *)

val differing : t -> node list
(** The nodes the engine itself holds: what differs from its bases, or may. *)

val unshared : t -> t -> node list
(** The nodes of an engine that may differ from another's. *)

val identity : node -> string
(** What names a node in every engine. *)

val count : t -> int
val label : node -> string
val subject : node -> Query.subject option
val is_input : node -> bool
val is_fixed : node -> bool
val reads : t -> node -> node list
val readers : t -> node -> node list
val counterpart : node -> t -> node option

val current_in : node -> t -> node option
(** The same query and key in another engine, computed there if it has none. *)

val same_outcome : t -> node -> t -> node -> bool

(** {1 States and facts in the store}

    A state is written as an artifact: the whole state, or what changed since an earlier artifact.
    Values are put in the store by fingerprint, and each saved result is also kept as a fact, under
    the key of what it read, so that any state whose reads have the same fingerprints finds it. *)

val attach : t -> Store.t -> version:string -> unit
(** Keeps the engine's values and facts in the store. [version] names what computed them, and is
    part of every key. *)

val record : t -> unit
(** Keeps a fact for each saved result computed since the last call. *)

val write : ?full:bool -> t -> string
(** Writes the state, and returns its artifact's name: a difference over the artifact it was opened
    from or last wrote, or with [~full:true], or when there is none, the whole state apart from its
    fixed bases. *)

type debt = Incremental.debt = { whole : int; differences : int; depth : int }

val debt : t -> debt
(** How many nodes the artifact chain's whole state holds, how many its differences hold, and how
    many differences there are, for deciding when to write the whole state again. *)

val unwritten : t -> bool
(** Whether the engine holds anything {!write} has not written. *)

val artifact : t -> string option
(** The artifact the engine last wrote, or was opened from. *)

val open_base : Store.t -> version:string -> bases:t list -> string -> t option
(** The whole state an artifact names, as a fixed frozen base: a package whose sources never change.
*)

val open_ : ?log:bool -> Store.t -> version:string -> bases:t list -> string -> t option
(** An engine for the state an artifact names, over fixed bases. The whole state its chain starts
    from is a frozen base, shared by every engine opened from it. [None] if the store no longer has
    the chain. *)

exception Lost of string
(** The store no longer has the value of an input a state holds, as after another process collected
    the store. The state cannot be used, and its session starts again from its files. *)

val inputs_stored : t -> bool
(** Whether the store still has the value of every input of the state, apart from its fixed bases'.
*)

val values_in : Store.t -> version:string -> string -> string list
(** Every name an artifact's chain refers to in the store, for collecting it; none for a chain that
    another version wrote, which only that version can read. *)

val forget_bases : unit -> unit

(** {1 Checking the engine} *)

val audit : ?flat:bool -> t -> string list
(** A line for each result that differs from what a new engine with the same inputs computes. *)

val audit_all : unit -> string list
(** Audits every engine made since {!auditing} was set that did work since its last audit. *)

val auditing : bool ref

val skip_audit : t -> unit
(** Leaves an engine out of {!audit_all}, for a test whose queries are not functions of what they
    read. *)
