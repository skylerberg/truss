module Symbol = Logic.Symbol

val zero : Logic.term

type target = Through of Logic.term | Capability of Path.t | Capability_method of Path.t * string
type resource = Time | Allocations | Allocated_bytes | Calls of target
type counting = Units | At_most | Exactly
type counter = { resource : resource; counting : counting; amortized : bool }

val covers : clause:target -> counter:target -> bool

type constants = { factor : Logic.symbol; addend : Logic.symbol; mutable pairs : (Z.t * Z.t) list }

val pairs : (Z.t * Z.t) list
val constants : Symbol.cost_group -> constants
val bound : constants -> Logic.term -> Logic.term
val pin : constants -> Z.t * Z.t -> Logic.term
val plus : Logic.term -> Logic.term -> Logic.term
val minus : Logic.term -> Logic.term -> Logic.term
val times : Logic.term -> Logic.term -> Logic.term
val at_most : Logic.term -> Logic.term -> Logic.term
val at_least_zero : Logic.term -> Logic.term
val larger : Logic.term -> Logic.term -> Logic.term
val units : Logic.term -> Logic.term
val log_facts : Logic.term -> halving:bool -> Logic.term list * Logic.term option
val log_order : Logic.term -> Logic.term -> Logic.term
val power_facts : Logic.term -> Logic.term -> Logic.term list * (Logic.term * Logic.term)
val power_order : Logic.term -> Logic.term -> Logic.term -> Logic.term
val normalize : Logic.term -> Logic.term
val since : start:Logic.term -> Logic.term -> Logic.term

type polarity = Grows | Shrinks | Both

val bound_on :
  varies:(Logic.term -> bool) -> facts:Logic.term list -> Logic.term -> Logic.term option

val upper_bounds :
  varies:(Logic.term -> bool) -> facts:Logic.term list -> Logic.term -> Logic.term list
