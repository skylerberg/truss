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

val key : Logic.query -> string
(** The cache key of a query: the hash of its canonical text together with the solver's version, its
    options, and its limit. *)

type request
(** A query as it is asked: its canonical text and key, and the canonical names of the symbols whose
    values a counterexample should give. *)

type canonical
(** An answer in a query's canonical names, which every query with the same text shares, so it can
    be kept by its request's key alone. *)

val request :
  ?values:Logic.symbol list -> ?terms:(Logic.symbol * Logic.term) list -> Logic.query -> request
(** [values] are the prover's symbols whose values a counterexample should give, and [terms] named
    terms whose values it should give, each by its name. *)

val request_key : request -> string

val ask_all : t -> request list -> canonical list
(** Runs each request, as {!ask} does, several at once, one for each core. *)

val read : request -> canonical -> answer
(** A canonical answer in the request's own symbols. *)

val solve : t -> ?values:Logic.symbol list -> Logic.query -> answer
(** Runs one query. [values] are the prover's symbols whose values a counterexample should give;
    those the query does not mention are left out. Results are cached by {!key} for the life of the
    process, and solving the same text twice gives the same answer. *)

val solved : t -> int
(** How many queries this solver has run itself, leaving out those answered from a cache: what
    incremental work's tests count. *)
