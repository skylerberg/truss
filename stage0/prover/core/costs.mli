val zero : Logic.term
val credit_symbol : Logic.symbol

type target = Through of Logic.term | Capability of Path.t | Capability_method of Path.t * string
type resource = Metric of Language.Metric.t | Calls of target
type counting = Units | At_most | Exactly
type counter = { resource : resource; counting : counting; amortized : bool }
type counted = No_potential | Potential_change | Potential_growth
type charge = { amount : Logic.term; counted : counted }

val make_counted_charge : counter -> Logic.term -> charge
val least_amount : resource -> Logic.term
val make_conditional_amount : Logic.term -> Logic.term -> Logic.term
val make_operand_counter : Language.Metric.t -> counter
val classify_counting : Mir.cost -> counting
val find_resource : Mir.cost -> locals:Logic.term Locals.t -> resource option
val is_same_resource : Mir.cost -> locals:Logic.term Locals.t -> counter -> bool

val list_stated_bounds :
  Types.cost list -> Language.Metric.t -> amortized:bool -> Types.cost_bound list

val states_no_allocation : Types.cost list -> bool
val find_stated_operand : Types.cost list -> Language.Metric.t -> Logic.term option
val bound : Logic.term -> Logic.term
val units : Logic.term -> Logic.term
val reduce_constants : Logic.term -> Logic.term
val since : start:Logic.term -> Logic.term -> Logic.term
val grows_with : varies:(Logic.term -> bool) -> Logic.term -> bool

val find_cost_bound :
  varies:(Logic.term -> bool) -> facts:Logic.term list -> Logic.term -> Logic.term option

val list_unbounded_parts :
  varies:(Logic.term -> bool) -> facts:Logic.term list -> Logic.term -> Logic.term list

val mentions_part : part:Logic.term -> Logic.term -> bool

val list_upper_bounds :
  varies:(Logic.term -> bool) -> facts:Logic.term list -> Logic.term -> Logic.term list

val mentions_potential : Logic.term -> bool
val list_potentials : Logic.term -> Logic.term list
val take_potential_as_zero : Logic.term -> Logic.term

val join_spent :
  (counter * Logic.term) list ->
  paths:(Logic.term * (Logic.term * Logic.term) list * (counter * Logic.term) list) list ->
  name:(Logic.term -> Logic.term) ->
  (counter * Logic.term) list
