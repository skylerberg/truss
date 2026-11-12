(** The engine's interface for the database: setting inputs, keeping results current, walking the
    graph, and keeping states and facts in the store. Only the database and tests use this; compiler
    stages see {!Query}. *)

type t = Incremental.t
(** One state: its differences from its bases, with the rest read from them. *)

val seal : unit -> unit
(** Rejects every input and query declared from now on. The database calls it before it opens a
    state, since a state leaves out the results that read a query not declared yet. *)

val create : ?log:bool -> ?bases:t list -> unit -> t
(** An engine over frozen bases. *)

val freeze : ?fixed:bool -> t -> unit
(** Brings an engine up to date and makes it a base, which never changes again. A [fixed] base is a
    package's whose sources never change, such as the standard library's. *)

val context : t -> Query.context
(** For a driver's reads, made outside any query. Each result read through it becomes a root: the
    engine maintains it across changes, with every result it reads, and never collects it. *)

val observer : t -> Query.context
(** For a driver's reads that make no root: a result is computed if the state has none, and is
    collected again unless something else makes it necessary. A question about a state is asked
    through this, so that asking does not change the results the state maintains. *)

val of_context : Query.context -> t
val set : t -> ('key, 'value) Query.input -> 'key -> 'value -> unit
val remove : t -> ('key, 'value) Query.input -> 'key -> unit

val get : t -> ('key, 'value) Query.query -> 'key -> 'value
(** A query's result, computed if needed, and a root from then on. *)

val unroot : t -> ('key, 'value) Query.query -> 'key -> unit
(** Makes a result no longer a root. One that is then unnecessary is collected. *)

type node = Incremental.node
type change = Incremental.change = { computed : node list; changed : node list }

val stabilize : t -> change
(** Brings every result the engine holds up to date, and returns the results computed since the last
    call, and those that came out different. *)

val executed : t -> string list
(** The results computed since the log was last cleared, as ["name(key)"]: for a check that nothing
    was computed, and for messages. A check of one result uses {!computed}. *)

val computed : t -> ('key, 'value) Query.query -> 'key list
(** The keys whose results of the query were computed since the log was last cleared, in order. *)

val result_label : ('key, 'value) Query.query -> 'key -> string
(** A result as {!executed} names it, for messages. *)

val clear_log : t -> unit

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
(** The work an engine has done since it was made. *)

(** {1 The graph} *)

val nodes : t -> node list
(** Every input and result of the state, apart from its fixed bases'. *)

val nodes_including_fixed : t -> node list

val differing : t -> node list
(** The nodes the engine itself holds: those that differ from its bases, or may. *)

val unshared : t -> t -> node list
(** The nodes of an engine that may differ from another's. *)

val identity : node -> string
(** A node's name in every engine. *)

val count : t -> int
val label : node -> string
val subject : node -> Query.subject option
val is_input : node -> bool
val is_fixed : node -> bool
val reads : t -> node -> node list
val readers : t -> node -> node list

val current_in : node -> t -> node option
(** The same query and key in another engine, computed there if it has none. The other engine only
    observes it, so it gains no root. *)

val same_outcome : t -> node -> t -> node -> bool

(** {1 States and facts in the store}

    A state is written as an artifact: the whole state, or its changes since an earlier artifact.
    Values are put in the store by fingerprint, and each saved result is also kept as a fact, under
    the key of its reads, so that any state whose reads have the same fingerprints finds it. *)

val attach : t -> Store.t -> version:string -> unit
(** Keeps the engine's values and facts in the store. [version] names the compiler that computed
    them, and is part of every key. *)

val record_facts : t -> unit
(** Keeps a fact for each saved result computed since the last call. *)

val write : ?full:bool -> t -> string
(** Writes the state, and returns its artifact's name: a difference over the artifact it was opened
    from or last wrote, or with [~full:true], or when there is none, the whole state apart from its
    fixed bases. *)

type chain_size = Incremental.chain_size = { whole : int; differences : int; depth : int }

val chain_size : t -> chain_size
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

val audit : ?include_bases:bool -> ?before:Query.phase -> t -> string list
(** A line for each result that differs from a new engine's result with the same inputs. With
    [before], only the results of the phases before that one are computed again, which leaves out
    results that are costly to compute and audited elsewhere, such as proofs. *)

val audit_all : unit -> string list
(** Audits every engine made since {!auditing} was set that did work since its last audit. *)

val auditing : bool ref

val skip_audit : t -> unit
(** Leaves an engine out of {!audit_all}, for a test whose queries are not pure functions of their
    reads. *)
