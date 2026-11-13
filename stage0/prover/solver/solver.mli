(** Running the pinned solver on one query.

    Each query runs in a fresh process, with a fixed limit in steps and a fixed seed, so its answer
    depends only on its text and the solver's version. *)

type t
(** A solver found on this machine, of the pinned version. *)

val find : ?cache:string -> unit -> (t, string) result
(** [$TRUSS_Z3], or [z3] on the path, checked to be the pinned version. With [cache], answers are
    also kept in that directory, one file per key, so a query solved once is never solved again on
    this machine. *)

type answer =
  | Proven  (** The goal cannot be false. *)
  | Counterexample of (Logic.symbol * string) list
      (** The goal can be false: the value of each requested symbol or term, as SMT-LIB text. *)
  | Out_of_steps  (** The solver could not decide within its limit. *)

type request
(** A query as it is asked: its key, and the canonical names of the symbols whose values a
    counterexample should give. It holds no text, so a run that keeps every request it makes does
    not keep every query's text. *)

type canonical
(** An answer in a query's canonical names, which every query with the same text shares, so it can
    be kept by its request's key alone. *)

val request :
  ?values:Logic.symbol list -> ?terms:(Logic.symbol * Logic.term) list -> Logic.query -> request
(** [values] are the prover's symbols whose values a counterexample should give, and [terms] named
    terms whose values it should give, each by its name. *)

val request_key : request -> string

val ask_all : t -> (request * Logic.query) list -> canonical list
(** Answers each request, several at once, one for each core, from a cache or else by running the
    solver on the query the request was made from. A query is rendered only to be run, and one whose
    text does not have the request's key raises [Invalid_argument], since its answer would be kept
    under another query's key and prove that query wrongly. *)

val read : request -> canonical -> answer
(** A canonical answer in the request's own symbols. *)

val solved : t -> int
(** How many queries this solver has run itself, leaving out those answered from a cache, as
    incremental work's tests count. *)

module For_testing : sig
  val key : Logic.query -> string
  (** The cache key of a query: the hash of its canonical text together with the solver's version,
      its options, and its limit. *)
end
