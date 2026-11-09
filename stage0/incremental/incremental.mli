(** The code database's engine: a graph of inputs and query results, kept current by pushing each
    change to what it can affect. See DATABASE.md, "Pushing changes".

    Compiler stages see this module only through {!Query}, and the database only through {!Engine}.
    Nothing else should name it. *)

exception Cycle of string list
(** A query asked, directly or through others, for its own result. The list names the queries on the
    cycle, from the one asked for again to the one that asked, as ["name(key)"]. Every query on the
    cycle has this as its outcome, whether or not it caught it, so a cycle is an error wherever it
    is met. *)

type subject = { path : Path.t; part : string option }
(** The definition, and the part of it, that a node is about. *)

type t
(** An engine: one session's graph, or a frozen layer that sessions share. *)

type context
(** What a running query reads through, or the engine itself for reads made outside any query, such
    as a driver's. *)

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
(** An input, which only the database sets. Its keys and values are saved with the graph. *)

val query :
  name:string ->
  show:('key -> string) ->
  ?saved:bool ->
  ?equal:('value -> 'value -> bool) ->
  ?about:('key -> subject option) ->
  (context -> 'key -> 'value) ->
  ('key, 'value) query
(** A query, computed by the function, which reads inputs and other queries only through the
    context. With [~saved:true] its results are saved with the graph, which needs its keys and
    values to hold no functions. [equal] decides early cutoff and defaults to structural equality.
*)

(** {1 Reading} *)

val read : context -> ('key, 'value) input -> 'key -> 'value option
(** An input's value, or [None] if it is not set. Either answer is read, so setting it later reaches
    the reader. *)

val demand : context -> ('key, 'value) query -> 'key -> 'value
(** A query's result, computed if it has none and brought up to date if a change may have reached
    it. Raises the exception the query raised, or {!Cycle}. *)

(** {1 Engines} *)

val create : ?log:bool -> ?shared:t -> unit -> t
(** An engine. With [~shared], it reads from that frozen layer every input the layer has set, and
    moves there every result computed only from the layer's inputs, so that other engines sharing
    the layer find it already done. With [~log:true] it keeps the log of {!executed}. *)

val frozen_layer : ?log:bool -> unit -> t
(** A frozen layer: an engine whose inputs are set once, before anything reads them. *)

val context : t -> context
(** Reads made outside any query. Every result read through it is kept current until {!release}. *)

val set : t -> ('key, 'value) input -> 'key -> 'value -> unit
(** Sets an input. If the value differs from what it was, every result that read it, directly or
    through others, is marked as possibly changed. Raises [Invalid_argument] while a query runs, and
    for a frozen layer's input that has been read. *)

val remove : t -> ('key, 'value) input -> 'key -> unit
(** Removes an input, as a change. *)

type change = { computed : node list; changed : node list }
(** What computing again found: each node computed again, and each whose result came out different,
    in the order they were computed. *)

val stabilize : t -> change
(** Brings every kept result up to date, and returns what was computed since the last stabilization.
*)

val release : t -> ('key, 'value) query -> 'key -> unit
(** No longer keeps a result current for reads made outside queries. A result nothing else reads is
    then dropped. *)

val executed : t -> string list
(** With [~log:true], the queries computed since the log was last cleared, as ["name(key)"], in the
    order they started. *)

val clear_log : t -> unit

(** {1 Nodes} *)

val label : node -> string
val subject : node -> subject option
val reads : node -> node list
val readers : node -> node list
val is_frozen : node -> bool

val nodes : t -> node list
(** Every node the engine holds, in the order they were made. *)

val counterpart : node -> t -> node option
(** The node with the same query or input and key in another engine, if it has one. *)

val same_outcome : node -> node -> bool
(** Whether two nodes of the same query or input and key hold equal results. *)

(** {1 Saving}

    The pieces {!Engine} saves and loads a graph from. *)

type saved_node = {
  id : int;
  name : string;
  key : string;  (** The key, marshaled *)
  value : string option;  (** The hash of the marshaled result, in the store *)
  reads : reference list;
  kept : bool;
}

and reference = Own of int | Frozen of string * string  (** A frozen node, by name and key *)

val changes_to_save : t -> saved_node list * int list
(** The saved nodes made or changed since the last call, with their values put in the store through
    [put], and the ids of saved nodes dropped since. Unsaved nodes are left out, and a saved node's
    reads go through them to the saved nodes and inputs they reach. *)

val everything_to_save : t -> saved_node list
(** Every saved node, for a journal's new base. *)

val set_store : t -> put:(string -> string) -> get:(string -> string option) -> unit
(** How the engine puts and gets marshaled values by hash. *)

val restore : t -> saved_node list -> unit
(** Fills an empty engine with saved nodes, whose values are read through [get] when first needed.
    Nodes of queries this program does not declare are left out, with every node that reads them. *)

val engine_of : context -> t
(** The engine a context reads from. *)
