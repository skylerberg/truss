(** Running the pinned solver on one query. See PROVER.md, "The solver".

    Each query runs in a fresh process, with a fixed limit in steps and a fixed seed, so its answer
    depends only on its text and the solver's version. *)

val version : string
(** The Z3 version the prover is pinned to. A different one is refused, since its answers could
    differ. *)

type t
(** A solver found on this machine, of the pinned version. *)

val find : unit -> (t, string) result
(** [$TRUSS_Z3], or [z3] on the path, checked to be the pinned version. *)

val steps : int
(** The limit in steps every query runs with. *)

type answer =
  | Proven  (** The goal cannot be false. *)
  | Counterexample of (string * string) list
      (** The goal can be false: the value of each requested symbol, as SMT-LIB text. *)
  | Out_of_steps  (** The solver could not decide within its limit. *)

val key : Logic.query -> string
(** The cache key of a query: the hash of its canonical text together with the solver's version, its
    options, and its limit. *)

val solve : t -> ?values:string list -> Logic.query -> answer
(** Runs one query. [values] are the prover's symbols whose values a counterexample should give;
    those the query does not mention are left out. Results are cached by {!key} for the life of the
    process, and solving the same text twice gives the same answer. *)
