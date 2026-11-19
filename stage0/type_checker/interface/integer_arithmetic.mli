type fixed = { bits : int; low : Z.t; high : Z.t }
type width = Fixed of fixed | Unbounded

type failure =
  | Out_of_range of Z.t
  | Zero_divisor
  | Least_value_over_minus_one
  | Shift_too_large of Z.t

val find_width : Types.ty -> width option
val add : width -> Z.t -> Z.t -> (Z.t, failure) result
val subtract : width -> Z.t -> Z.t -> (Z.t, failure) result
val multiply : width -> Z.t -> Z.t -> (Z.t, failure) result
val divide : width -> Z.t -> Z.t -> (Z.t, failure) result
val remainder : width -> Z.t -> Z.t -> (Z.t, failure) result
val negate : width -> Z.t -> (Z.t, failure) result
val complement : fixed -> Z.t -> Z.t
val shift_left : fixed -> Z.t -> amount:Z.t -> (Z.t, failure) result
val shift_right : fixed -> Z.t -> amount:Z.t -> (Z.t, failure) result
