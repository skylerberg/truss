val make_signature : Intrinsic.operation -> Types.signature

type time = Constant_time | Linear_in of int | Unbounded_time
type amount = Argument of int | Generic of string
type allocations = No_allocations | One_if_positive of amount | Unknown_allocations
type cost = { time : time; allocations : allocations }

val classify_cost : Intrinsic.operation -> cost
