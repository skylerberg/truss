(** The signatures of [standard::intrinsic]'s operations, as data the type checker and code
    generation both read. *)

val signature : Intrinsic.operation -> Types.signature
(** Each generic parameter is owned by the operation's path. *)

type cost = { constant_time : bool; allocation_free : bool }

val cost : Intrinsic.operation -> cost
(** What an operation costs, which the prover trusts: whether it takes a fixed number of steps, and
    whether it never allocates. An operation that does more is known by no bound. *)
