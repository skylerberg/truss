(** What a compiler stage sees of the code database: declaring inputs and queries, and reading them
    while a query runs. See DATABASE.md, "The interfaces".

    A query is a pure function of what it reads through its context. The database records each read,
    and when something changes, computes again only the results that read it, directly or through
    others, stopping wherever a result comes out the same. A stage never sets an input, never names
    a session, and cannot tell whether it runs in the background process, in a test, or for a
    commit. *)

type context = Incremental.context
(** What a running query reads through. A driver gets one from the database for reads made outside
    any query. *)

type subject = Incremental.subject = { path : Path.t; part : string option }
(** The definition, and the part of it, that a result is about, for answering questions about
    dependencies by definition. *)

type ('key, 'value) input = ('key, 'value) Incremental.input

val input :
  name:string ->
  show:('key -> string) ->
  ?equal:('value -> 'value -> bool) ->
  ?about:('key -> subject option) ->
  unit ->
  ('key, 'value) input
(** An input, which only the database sets. [show] names a key in logs and messages. *)

type ('key, 'value) query = ('key, 'value) Incremental.query

val query :
  name:string ->
  show:('key -> string) ->
  ?saved:bool ->
  ?equal:('value -> 'value -> bool) ->
  ?about:('key -> subject option) ->
  (context -> 'key -> 'value) ->
  ('key, 'value) query
(** A query, computed by the function. With [~saved:true] its results are saved with the graph, so a
    new process finds them done; its keys and values must then hold no functions. [equal] decides
    early cutoff, and defaults to structural equality, so a value must not hold functions unless
    [equal] is given. *)

val get : context -> ('key, 'value) input -> 'key -> 'value
(** An input's value. Raises [Not_found] if it is not set; either answer is read. *)

val find : context -> ('key, 'value) input -> 'key -> 'value option
(** An input's value, or [None] if it is not set. *)

val demand : context -> ('key, 'value) query -> 'key -> 'value
(** A query's result. Raises the exception the query raised, or {!Cycle}. *)

exception Cycle of string list
(** A query asked, directly or through others, for its own result. Every query on the cycle has this
    as its result, whether it caught it or not, so a stage cannot rely on catching it. *)
