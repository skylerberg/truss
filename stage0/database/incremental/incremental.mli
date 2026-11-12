(** The code database's engine: one state's inputs and query results, kept current by pushing each
    change, phase by phase, to the readers of the values that really changed.

    Compiler stages see this module only through {!Query}, and the database only through {!Engine}.
    Nothing else should name it. *)

exception Cycle of string list
(** A query asked, directly or through others, for its own result. The list names the queries on the
    cycle, from the one asked for again to the one that asked, as ["name(key)"]. Every query on the
    cycle has this as its outcome, whether or not it caught it, so a cycle is an error wherever it
    is met. *)

exception Lost of string
(** The store no longer has the value of an input that a state holds, which names the input. The
    state cannot be used: an input's value comes from the database and cannot be recomputed. It is
    never a query's outcome. *)

type subject = { path : Path.t; part : string option }
(** The definition, and the part of it, that a result is about. *)

type t
(** An engine: one state. It holds its differences from its bases, and reads the rest from them. *)

type context
(** The context a running query reads through, or the engine itself for reads made outside any
    query, such as a driver's. *)

type node
(** An input or a query result, in one engine. *)

type ('key, 'value) input
type ('key, 'value) query

(** {1 Declaring} *)

val input :
  name:string ->
  show:('key -> string) ->
  ?equal:('value -> 'value -> bool) ->
  ?about:('key -> subject option) ->
  unit ->
  ('key, 'value) input
(** An input, which only the database sets. Its keys and values are saved with a state. *)

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
(** A query, computed by the function, which reads inputs and other queries only through the
    context. Its phase orders it among the queries: it may read queries of its own phase and of
    earlier ones, and reading a later one raises [Invalid_argument]. With [~saved:true] its results'
    bytes are kept in the store and each is a fact, which needs its keys and values to hold no
    functions. With [~portable:true] a saved result is also looked for as a fact in a state that has
    never held one, for which the store keeps such a result's dependencies, by name. [equal] decides
    whether a result came out the same, and defaults to structural equality. *)

val seal : unit -> unit
(** After this, declaring an input or a query raises [Invalid_argument]. The database calls it when
    it first opens its store: a state opened before a query is declared leaves out every result that
    read one, so a query declared later, as one inside a lazy value is, would have its readers
    computed again in every process. *)

val phases : int
(** Phases run from 1 to [phases - 1]. Inputs are in phase 0. *)

(** {1 Reading} *)

val read : context -> ('key, 'value) input -> 'key -> 'value option
(** An input's value, or [None] if it is not set. Either answer is read, so setting it later reaches
    the reader. *)

val demand : context -> ('key, 'value) query -> 'key -> 'value
(** A query's result, computed if it has none. Raises the exception the query raised, or {!Cycle}. A
    demand made outside any query first brings the state up to date through the query's phase; later
    phases keep their queued results until something of theirs is read, or {!stabilize}. *)

(** {1 Engines} *)

val create : ?log:bool -> ?bases:t list -> unit -> t
(** An engine over frozen bases: it reads every input and result they hold, and holds itself only
    the results it sets, computes, or finds changed. With [~log:true] it keeps the log of
    {!executed}. *)

val freeze : ?fixed:bool -> t -> unit
(** Brings the engine up to date and makes it a base: nothing in it changes again. A [fixed] base's
    inputs are a package's whose sources never change, such as the standard library's; the others
    are an earlier state of the code being worked on. *)

val context : t -> context

val observer : t -> context
(** A driver's context whose reads make no root: a result read through it is computed if the state
    has none, and collected again if nothing else makes it necessary. *)

val engine_of : context -> t
(** The engine a context reads from. *)

val set : t -> ('key, 'value) input -> 'key -> 'value -> unit
(** Sets an input. If the value differs from the engine's, the input's dependents are brought up to
    date at the next read or {!stabilize}. Raises [Invalid_argument] while a query runs, and for a
    frozen engine. *)

val remove : t -> ('key, 'value) input -> 'key -> unit
(** Removes an input, as a change. *)

type change = { computed : node list; changed : node list }
(** The work of bringing an engine up to date: each result computed, and each that came out
    different, in the order they were computed. *)

val stabilize : t -> change
(** Brings every result the engine holds up to date, and returns the results computed since the last
    call. *)

val unroot : t -> ('key, 'value) query -> 'key -> unit
(** Makes a result no longer a root. One that is then unnecessary is collected, with the nodes only
    it read. *)

val executed : t -> string list
(** With [~log:true], the queries computed since the log was last cleared, as ["name(key)"], in the
    order they started: for a check that nothing was computed, and for messages. *)

val computed : t -> ('key, 'value) query -> 'key list
(** With [~log:true], the keys whose results of the query were computed since the log was last
    cleared, in the order they started. *)

val result_label : ('key, 'value) query -> 'key -> string
(** A result's label in {!executed}: ["name(key)"]. *)

val clear_log : t -> unit

type counters = {
  marked : int;  (** Results marked as possibly changed *)
  confirmed : int;  (** Marked results found current without computing them *)
  computed : int;  (** Results computed *)
  changed : int;  (** Results that came out different *)
  adopted : int;  (** Results found as facts in the store instead of computed *)
  copied : int;  (** Results of a base copied into the engine, to be checked there *)
  collected : int;  (** Unnecessary results collected *)
}

val counters : t -> counters
(** The work the engine has done since it was made. Tests compare these at two sizes of a project,
    to hold that a change's cost follows the change. *)

(** {1 The graph} *)

val label : node -> string
val subject : node -> subject option
val is_input : node -> bool

val nodes : t -> node list
(** Every input and result of the state, apart from those of its fixed bases, in the order they were
    made. *)

val count : t -> int
(** How many inputs and results the engine itself holds. *)

val is_fixed : node -> bool
(** Whether a node belongs to a fixed base. *)

val reads : t -> node -> node list
(** A result's dependencies when it was last computed, in order, as the engine sees each. *)

val readers : t -> node -> node list
(** A node's readers, as the engine sees it. *)

val differing : t -> node list
(** The nodes the engine itself holds: those that differ from its bases, or may. *)

val unshared : t -> t -> node list
(** The nodes of an engine that may differ from another's: those it holds itself, and those of each
    base, apart from fixed ones, that the other does not also have. *)

val identity : node -> string
(** A node's name in every engine: a hash of its input or query and its key. *)

val current_in : node -> t -> node option
(** The same, computed there if it is a result the other engine does not have; for an input, the
    same input if the other engine has a cell for it. *)

val same_outcome : t -> node -> t -> node -> bool
(** Whether two nodes of the same query or input and key, each in its engine, hold equal results. *)

(** {1 Facts and states in a store} *)

type store = {
  id : string;  (** The store's identity: its directory *)
  version : string;
      (** The compiler that computed the results: its identity. It is part of every key. *)
  put : string -> string;  (** Keeps bytes, and returns their name: their hash *)
  get : string -> string option;
  find : kind:string -> key:string -> string option;
  add : kind:string -> key:string -> string -> unit;  (** Keeps a result under a key, once *)
}
(** How an engine keeps values by fingerprint, and facts by key. *)

val attach : t -> store -> unit

val record_facts : t -> unit
(** Keeps a fact for each saved result computed since the last call: its value under the key of its
    reads. Another state whose reads have the same fingerprints finds it instead of computing.
    {!write} does this too. *)

val write : ?full:bool -> t -> string
(** Writes the state as an artifact in the store, and returns its name. The artifact holds the
    engine's own nodes that changed since the last write, as a difference over the artifact the
    engine was opened from or last wrote; with [~full:true], or when there is no such artifact, it
    holds the whole state apart from its fixed bases. *)

type chain_size = { whole : int; differences : int; depth : int }
(** How many nodes the whole state an engine's artifact chain starts from holds, how many the
    differences after it hold, and how many differences there are. *)

val chain_size : t -> chain_size

val unwritten : t -> bool
(** Whether the engine holds anything {!write} has not written. *)

val artifact : t -> string option
(** The artifact the engine last wrote, or was opened from. *)

val open_ : ?log:bool -> store -> bases:t list -> string -> t option
(** An engine for the state an artifact names, over the given fixed bases: the artifact's chain is
    followed to the whole state it starts from, which is loaded as a frozen base and shared by every
    engine opened from it, and the differences after it are the engine's own. [None] if the store no
    longer has the chain. Values are read from the store when first needed. *)

val frozen_of : store -> bases:t list -> fixed:bool -> string -> t option
(** The whole state an artifact names, as a frozen base. *)

val inputs_stored : t -> bool
(** Whether the store still has the value of every input of the state, apart from its fixed bases'.
*)

val values_in : store -> string -> string list
(** Every name an artifact's chain refers to in the store, itself included, for collecting the
    store. *)

val forget_bases : unit -> unit
(** Drops the frozen bases kept for sharing between engines, as a new process starts without. *)

(** {1 Checking the engine} *)

val audit : ?include_bases:bool -> ?before:int -> t -> string list
(** Brings the engine up to date, then computes every result it holds in a new engine with the same
    inputs, and returns a line for each that differs. With [~include_bases:true] the new engine has
    no bases and is given their inputs too, which checks the bases' results as well as its own. With
    [before], only the results of the phases before that one are computed again. An empty list means
    every result equals a fresh computation's. *)

val auditing : bool ref
(** When set, every engine made is remembered, weakly, for {!audit_all}. *)

val audit_all : unit -> string list
(** Audits every remembered engine that did work since its last audit. *)

val skip_audit : t -> unit
(** Leaves an engine out of {!audit_all}: one whose queries are, for a test, not functions of their
    reads. *)
