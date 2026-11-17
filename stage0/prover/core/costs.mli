val zero : Logic.term

type target = Through of Logic.term | Capability of Path.t | Capability_method of Path.t * string
type resource = Metric of Metric.t | Calls of target
type counting = Units | At_most | Exactly
type counter = { resource : resource; counting : counting; amortized : bool }

val least_amount : resource -> Logic.term
val make_operand_counter : Metric.t -> counter
val list_stated_bounds : Types.cost list -> Metric.t -> Types.cost_bound list
val find_stated_operand : Types.cost list -> Metric.t -> Logic.term option
val bound : Logic.term -> Logic.term
val plus : Logic.term -> Logic.term -> Logic.term
val minus : Logic.term -> Logic.term -> Logic.term
val times : Logic.term -> Logic.term -> Logic.term
val at_most : Logic.term -> Logic.term -> Logic.term
val at_least_zero : Logic.term -> Logic.term
val larger : Logic.term -> Logic.term -> Logic.term
val units : Logic.term -> Logic.term
val normalize : Logic.term -> Logic.term
val since : start:Logic.term -> Logic.term -> Logic.term

val find_cost_bound :
  varies:(Logic.term -> bool) -> facts:Logic.term list -> Logic.term -> Logic.term option

val list_upper_bounds :
  varies:(Logic.term -> bool) -> facts:Logic.term list -> Logic.term -> Logic.term list
