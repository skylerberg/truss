type fixed = { bits : int; low : Z.t; high : Z.t }
type width = Fixed of fixed | Unbounded

type failure =
  | Out_of_range of Z.t
  | Zero_divisor
  | Least_value_over_minus_one
  | Shift_too_large of Z.t

let find_width type_ =
  match (Types.find_integer_bits type_, Types.find_integer_range type_) with
  | Some (bits, _), Some (low, high) -> Some (Fixed { bits; low; high })
  | _ -> if Types.is_builtin Integer type_ then Some Unbounded else None

let fit width result =
  match width with
  | Fixed { low; high; _ } when Z.lt result low || Z.gt result high -> Error (Out_of_range result)
  | Fixed _ | Unbounded -> Ok result

let add width left right = fit width (Z.add left right)
let subtract width left right = fit width (Z.sub left right)
let multiply width left right = fit width (Z.mul left right)
let negate width value = fit width (Z.neg value)

let divide_by operation width left right =
  if Z.equal right Z.zero then Error Zero_divisor
  else
    match width with
    | Fixed { low; _ } when Z.sign low < 0 && Z.equal left low && Z.equal right Z.minus_one ->
        Error Least_value_over_minus_one
    | Fixed _ | Unbounded -> fit width (operation left right)

let divide = divide_by Z.div
let remainder = divide_by Z.rem

let complement { low; high; _ } value =
  if Z.sign low < 0 then Z.lognot value else Z.logxor value high

let shift_by operation { bits; low; _ } value ~amount =
  if Z.sign amount < 0 || Z.geq amount (Z.of_int bits) then Error (Shift_too_large amount)
  else
    let shifted = operation value (Z.to_int amount) in
    Ok (if Z.sign low < 0 then Z.signed_extract shifted 0 bits else Z.extract shifted 0 bits)

let shift_left = shift_by Z.shift_left
let shift_right = shift_by Z.shift_right
