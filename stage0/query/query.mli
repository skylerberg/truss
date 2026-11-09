(** What a compiler stage sees of the code database: declaring inputs and queries, and reading them
    while a query runs. See DATABASE.md, "The interfaces".

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

(** The compiler's phases, in order. A query reads queries of its own phase and of earlier ones,
    never of a later one, so that when the database brings a phase up to date, every earlier one is
    final, and a result that comes out the same in one phase costs the later ones nothing. *)
type phase =
  | Syntax  (** A file's tokens and trees *)
  | Declarations  (** What each file and package declares, and finding a definition by name *)
  | Resolution  (** What each name in a definition means *)
  | Interfaces  (** Signatures, shapes, constants, and the [impl]s found for a type *)
  | Bodies  (** Checked bodies, and what is found in them *)
  | Checks  (** The rules that span a package *)
  | Diagnostics  (** Every stage's diagnostics for a file *)
  | Lowering  (** What each instance compiles to *)
  | Linking  (** What each instance refers to, and the hash of its own code *)
  | Recursion  (** Which instances reach themselves *)
  | Keys  (** The key of everything an instance can reach *)

val phase_name : phase -> string

type ('key, 'value) query = ('key, 'value) Incremental.query

val query :
  name:string ->
  show:('key -> string) ->
  phase:phase ->
  ?saved:bool ->
  ?equal:('value -> 'value -> bool) ->
  ?about:('key -> subject option) ->
  (context -> 'key -> 'value) ->
  ('key, 'value) query
(** A query of a phase, computed by the function. With [~saved:true] its results are saved with a
    state and kept as facts, so another state or process finds them done; its keys and values must
    then hold no functions. [equal] decides whether a result came out the same, and defaults to
    structural equality, so a value must not hold functions unless [equal] is given. Reading a query
    of a later phase raises [Invalid_argument]. *)

val get : context -> ('key, 'value) input -> 'key -> 'value
(** An input's value. Raises [Not_found] if it is not set; either answer is read. *)

val find : context -> ('key, 'value) input -> 'key -> 'value option
(** An input's value, or [None] if it is not set. *)

val demand : context -> ('key, 'value) query -> 'key -> 'value
(** A query's result. Raises the exception the query raised, or {!Cycle}. *)

exception Cycle of string list
(** A query asked, directly or through others, for its own result. Every query on the cycle has this
    as its result, whether it caught it or not, so a stage cannot rely on catching it. *)
