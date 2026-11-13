(** The signatures of [standard::intrinsic]'s operations, as data the type checker and code
    generation both read. *)

val signature : Intrinsic.operation -> Types.signature
(** Each generic parameter is owned by the operation's path. *)

type time =
  | Constant_time
  | Linear_in of int
      (** Steps in proportion to the length of the storage or view that is this argument. *)
  | Unbounded_time

(** A number an operation is given: the argument at a position, or a [USize] generic argument by its
    name. *)
type amount = Argument of int | Generic of string

(** How many blocks an operation allocates. *)
type allocations =
  | No_allocations
  | One_if_positive of amount  (** One when this amount is above zero, and otherwise none. *)
  | Unknown_allocations

type cost = { time : time; allocations : allocations }

val cost : Intrinsic.operation -> cost
(** An operation's cost, which the prover trusts: how many steps it takes, and how many blocks it
    allocates. An operation that does more is known by no bound. *)
