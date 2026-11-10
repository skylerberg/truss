(** The signatures of [standard::intrinsic]'s operations, as data the type checker and code
    generation both read. *)

val signature : Intrinsic.operation -> Types.signature
(** Each generic parameter is owned by the operation's path. *)

type time =
  | Constant_time
  | Linear_in of int
      (** Steps in proportion to the length of the storage or view that is this argument. *)
  | Unbounded_time

type cost = { time : time; allocation_free : bool }

val cost : Intrinsic.operation -> cost
(** What an operation costs, which the prover trusts: how many steps it takes, and whether it never
    allocates. An operation that does more is known by no bound. *)
