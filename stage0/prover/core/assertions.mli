val assertion :
  State.context ->
  State.frame ->
  origin:int ->
  bit_vector:((Core.local * Types.ty) list * (State.frame -> Logic.term)) option ->
  Logic.term ->
  unit
