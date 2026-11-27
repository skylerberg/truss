val check_assertion :
  State.frame ->
  origin:Core.origin ->
  bit_vector:((Core.local * Types.ty) list * (State.frame -> Logic.term)) option ->
  Logic.term ->
  unit
