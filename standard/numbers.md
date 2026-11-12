# Methods of the number types

The files in `standard/numbers/` define the methods of the built-in integer
and float types. They are not imported: the methods are called on the
values.

- `checked_add` returns an `Option`, and `wrapping_add` and `saturating_add`
  wrap or saturate. Subtraction, multiplication, and powers have the same
  three versions, and division and remainder have a checked one.
- `floor_divide` and `floor_modulo` round down, where `/` and `%` round
  toward zero.
- `Int64.from(value)` converts where no information can be lost, and
  `UInt32.try_from(value)` returns a `Result` where it can.
- A provided method of `FixedWidthInteger`, `SignedInteger`, or
  `UnsignedInteger`, such as `checked_power`, is a method of every width.
  `minimum_value()`, `maximum_value()`, and `bit_width()` give a type's
  bounds in generic code.
- `x.is_nan()` tests for NaN. `ieee_equal`, `ieee_less`, and the other
  `ieee_` comparisons follow IEEE 754 exactly, and compile to one
  instruction.
- `sin`, `exp`, and the conversions between floats and text are written in
  Truss, so they give the same bits on every platform. `to_bits()` returns
  one bit pattern for every NaN.
