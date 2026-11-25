val zero : Logic.term

type target = Through of Logic.term | Capability of Path.t | Capability_method of Path.t * string
type resource = Metric of Language.Metric.t | Calls of target
type counting = Units | At_most | Exactly

type counter = {
  resource : resource;
  counting : counting;
  amortized : bool;
  counts_potential : bool;
}

type counted = No_potential | Potential_change | Potential_growth
type charge = { amount : Logic.term; counted : counted }

val make_counted_charge : counter -> Logic.term -> charge
val least_amount : resource -> Logic.term
val make_operand_counter : Language.Metric.t -> counter
val list_checking_counters : counter -> counter list

val list_stated_bounds :
  Types.cost list -> Language.Metric.t -> amortized:bool -> Types.cost_bound list

val find_stated_operand : Types.cost list -> Language.Metric.t -> Logic.term option
val bound : Logic.term -> Logic.term
val plus : Logic.term -> Logic.term -> Logic.term
val minus : Logic.term -> Logic.term -> Logic.term
val times : Logic.term -> Logic.term -> Logic.term
val at_least_zero : Logic.term -> Logic.term
val larger : Logic.term -> Logic.term -> Logic.term
val reduce_constants : Logic.term -> Logic.term
val units : Logic.term -> Logic.term
val linearize : Logic.term -> (Logic.term * Z.t) list * Z.t
val combine : (Logic.term * Z.t) list * Z.t -> Logic.term
val normalize : Logic.term -> Logic.term
val since : start:Logic.term -> Logic.term -> Logic.term
val grows_with : varies:(Logic.term -> bool) -> Logic.term -> bool

val find_cost_bound :
  varies:(Logic.term -> bool) -> facts:Logic.term list -> Logic.term -> Logic.term option

val list_unbounded_parts :
  varies:(Logic.term -> bool) -> facts:Logic.term list -> Logic.term -> Logic.term list

val mentions_part : part:Logic.term -> Logic.term -> bool

val list_upper_bounds :
  varies:(Logic.term -> bool) -> facts:Logic.term list -> Logic.term -> Logic.term list
