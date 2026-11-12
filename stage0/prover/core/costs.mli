module L = Logic
module S = Logic.Symbol

val zero : L.term

type target = Through of L.term | Capability of Path.t | Capability_method of Path.t * string
type resource = Time | Allocations | Allocated_bytes | Calls of target
type counting = Units | At_most | Exactly
type counter = { resource : resource; counting : counting; amortized : bool }

val key : counter -> string
val covers : clause:target -> counter:target -> bool

type constants = { factor : S.t; addend : S.t; mutable pairs : (Z.t * Z.t) list }

val pairs : (Z.t * Z.t) list
val constants : S.cost_group -> constants
val bound : constants -> L.term -> L.term
val pin : constants -> Z.t * Z.t -> L.term
val plus : L.term -> L.term -> L.term
val minus : L.term -> L.term -> L.term
val times : L.term -> L.term -> L.term
val at_most : L.term -> L.term -> L.term
val at_least_zero : L.term -> L.term
val larger : L.term -> L.term -> L.term
val units : L.term -> L.term
val log_facts : L.term -> halving:bool -> L.term list * L.term option
val log_order : L.term -> L.term -> L.term
val power_facts : L.term -> L.term -> L.term list * (L.term * L.term)
val power_order : L.term -> L.term -> L.term -> L.term
val normalize : L.term -> L.term
val since : start:L.term -> L.term -> L.term

type polarity = Grows | Shrinks | Both

val bound_on : varies:(L.term -> bool) -> facts:L.term list -> L.term -> L.term option
val upper_bounds : varies:(L.term -> bool) -> facts:L.term list -> L.term -> L.term list
