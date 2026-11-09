(** Demand-driven queries with verifying traces. See TYPECHECKER.md, "One definition at a time,
    through queries", and DESIGN.md, "Incremental builds".

    A {e database} holds {e inputs}, which the driver sets, and the stored results of {e queries},
    which are functions of inputs and of other queries. Each stored result keeps a trace: every
    input and query it read while it ran. When inputs change, a result is reused if everything in
    its trace still gives the same answer, and otherwise is computed again. A result that comes out
    the same as before counts as unchanged, so the results that read it are reused too: this is
    early cutoff, and it is what makes a body edit re-check no caller.

    This is the scheme of "Build Systems à la Carte" (verifying traces), and of rustc's queries and
    Salsa: each result records the revision it was last checked at and the revision its value last
    changed at, and a trace entry is unchanged when its value has not changed since the result that
    read it was checked. *)

type database

val create : unit -> database

type ('key, 'value) input

val input :
  name:string ->
  show:('key -> string) ->
  ?equal:('value -> 'value -> bool) ->
  unit ->
  ('key, 'value) input
(** An input. [show] names a key in the log and in errors. [equal] decides whether setting a value
    changes it, and defaults to structural equality. *)

val set : database -> ('key, 'value) input -> 'key -> 'value -> unit
(** Sets an input. If the value differs from what it was, the database moves to a new revision, and
    every result that read it is checked again when next asked for. *)

val remove : database -> ('key, 'value) input -> 'key -> unit
(** Removes an input, as a change: a later {!get} of it raises [Not_found]. *)

val get : database -> ('key, 'value) input -> 'key -> 'value
(** Reads an input, recording it in the trace of the query that is running. Raises [Not_found] if it
    was never set. *)

val find : database -> ('key, 'value) input -> 'key -> 'value option
(** Like {!get}, but [None] for an input that is not set, which is recorded too, so setting it later
    re-runs the reader. *)

type ('key, 'value) query

val query :
  name:string ->
  show:('key -> string) ->
  ?equal:('value -> 'value -> bool) ->
  (database -> 'key -> 'value) ->
  ('key, 'value) query
(** A query, computed by the function, which reads inputs and other queries only through this
    module. [equal] decides early cutoff and defaults to structural equality, so a value must not
    hold functions unless [equal] is given. *)

val demand : database -> ('key, 'value) query -> 'key -> 'value
(** The query's result for the key: stored, checked against its trace, or computed. Raises {!Cycle}
    if the query is already running for that key. *)

exception Cycle of string list
(** A query asked, directly or through others, for its own result. The list names the queries on the
    cycle, from the one asked for again to the one that asked, as ["name(key)"]. *)

(** {1 Observing work}

    For tests of incremental behavior, which assert exactly which queries ran again. *)

val executed : database -> string list
(** The queries that ran since the log was last cleared, as ["name(key)"], in the order they
    started. *)

val clear_log : database -> unit
