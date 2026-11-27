val make_signature : Intrinsic.operation -> Types.signature

type time = Constant_time | Linear_in of int | Linear_in_result | Unbounded_time
type allocations = No_allocations | Unknown_allocations
type cost = { time : time; allocations : allocations }

val classify_cost : Intrinsic.operation -> cost
