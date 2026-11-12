(** What a compiler stage sees of the code database: declaring inputs and queries, and reading them
    while a query runs.

    A query is a pure function of what it reads through its context. The database records each read,
    and when something changes, computes again only the results that read what really changed,
    stopping wherever a result comes out the same. A stage never sets an input, never names a
    session, and cannot tell whether it runs in the background process, in a test, or for a commit.
*)

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

type phase
(** A phase: a step in the order in which a change is pushed through the queries. A query reads
    queries of its own phase and of the phases its phase was declared after, never of a later one,
    so that when the database brings a phase up to date, every earlier one is final, and a result
    that comes out the same in one phase costs the later ones nothing. The database holds no list of
    phases: whoever declares the queries declares their phases. *)

val phase : name:string -> after:phase list -> phase
(** A phase whose queries may read the phases in [after], and every phase those were declared after.
    Raises [Invalid_argument] for a name used twice. *)

val phase_rank : phase -> int
(** A phase's place in the order, for the engine: lower for a phase that a higher one may read. *)

type ('key, 'value) query = ('key, 'value) Incremental.query

val query :
  name:string ->
  show:('key -> string) ->
  phase:phase ->
  ?saved:bool ->
  ?portable:bool ->
  ?equal:('value -> 'value -> bool) ->
  ?about:('key -> subject option) ->
  (context -> 'key -> 'value) ->
  ('key, 'value) query
(** A query of a phase, computed by the function. With [~saved:true] its results' bytes are kept in
    the store, and each is a fact that a state finds once it has held a result of the same key; its
    keys and values must then hold no functions. With [~portable:true] a state that has never held
    one finds it too, which suits results that many states come to need without starting from one
    another, such as what an instance of the standard library compiles to. [equal] decides whether a
    result came out the same, and defaults to structural equality, so a value must not hold
    functions unless [equal] is given. Reading a query of a later phase raises [Invalid_argument].
*)

val get : context -> ('key, 'value) input -> 'key -> 'value
(** An input's value. Raises [Not_found] if it is not set; either answer is read. *)

val find : context -> ('key, 'value) input -> 'key -> 'value option
(** An input's value, or [None] if it is not set. *)

val demand : context -> ('key, 'value) query -> 'key -> 'value
(** A query's result. Raises the exception the query raised, or {!Cycle}. *)

val known : context -> ('key, 'value) query -> 'key -> 'value option
(** For a driver, outside any query: the result the state already holds for a query and key, if no
    change could have reached it. The phases before the query's are brought up to date, and nothing
    of the query's own phase is computed, so a driver can tell which results are still to be
    computed and prepare for them together, as the prover solves many definitions' queries at once.
    [None] is also the answer for a result whose reads may have changed, even where checking them
    would find it current, and for one that raised. The read is not recorded and the result is not
    kept. Raises [Invalid_argument] inside a running query. *)

exception Cycle of string list
(** A query asked, directly or through others, for its own result. Every query on the cycle has this
    as its result, whether it caught it or not, so a stage cannot rely on catching it. *)
