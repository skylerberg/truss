(** The signatures of [standard::intrinsic]'s operations, as data the type checker and code
    generation both read. *)

val signature : Intrinsic.operation -> Types.signature
(** Each generic parameter is owned by the operation's path. *)

type time =
  | Constant_time
  | Linear_in of int
      (** Steps in proportion to the length of the storage or view that is this argument. *)
  | Unbounded_time

(** How many blocks an operation allocates. *)
type allocations =
  | No_allocations
  | One_if_positive of int
      (** One when the argument at this position is above zero, which is the room it makes. *)
  | Unknown_allocations

type cost = { time : time; allocations : allocations }

val cost : Intrinsic.operation -> cost
(** What an operation costs, which the prover trusts: how many steps it takes, and how many blocks
    it allocates. An operation that does more is known by no bound. *)
