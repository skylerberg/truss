let round_float ~precision ~minimum ~maximum ~(significand : Z.t) ~(exponent : Z.t) : float option =
  if Z.equal significand Z.zero then Some 0.0
  else
    let negative = Z.sign significand < 0 in
    let magnitude = Z.abs significand in
    let power = Z.pow (Z.of_int 10) (Z.to_int (Z.abs exponent)) in
    let numerator, denominator =
      if Z.sign exponent >= 0 then (Z.mul magnitude power, Z.one) else (magnitude, power)
    in
    let estimate = Z.numbits numerator - Z.numbits denominator in
    let at_least expression =
      if expression >= 0 then Z.geq numerator (Z.mul denominator (Z.shift_left Z.one expression))
      else Z.geq (Z.shift_left numerator (-expression)) denominator
    in
    let expression = if at_least estimate then estimate else estimate - 1 in
    let expression = max expression minimum in
    let scale = expression - precision + 1 in
    let scaled_numerator, scaled_denominator =
      if scale >= 0 then (numerator, Z.shift_left denominator scale)
      else (Z.shift_left numerator (-scale), denominator)
    in
    let quotient, remainder = Z.ediv_rem scaled_numerator scaled_denominator in
    let twice = Z.shift_left remainder 1 in
    let rounded =
      let compared = Z.compare twice scaled_denominator in
      if compared > 0 || (compared = 0 && Z.is_odd quotient) then Z.succ quotient else quotient
    in
    let rounded, scale =
      if Z.geq rounded (Z.shift_left Z.one precision) then (Z.shift_right rounded 1, scale + 1)
      else (rounded, scale)
    in
    if scale + precision - 1 > maximum then None
    else
      let value = Float.ldexp (Z.to_float rounded) scale in
      Some (if negative then -.value else value)

let round_float32 ~significand ~exponent =
  round_float ~precision:24 ~minimum:(-126) ~maximum:127 ~significand ~exponent

let round_float64 ~significand ~exponent =
  round_float ~precision:53 ~minimum:(-1022) ~maximum:1023 ~significand ~exponent
