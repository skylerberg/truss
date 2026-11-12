type group =
  | Arithmetic
  | Shift
  | Bitwise of Syntax.binary
  | Range_group
  | Comparison
  | And_group
  | Or_group
  | Implies_group
  | Lowest

type grouping = Left_first | Right_first
type problem = Lowest_operand | Chained of string | Mixed of string | Mixed_bitwise

val expression : ?context:group * bool -> Cursor.t -> Syntax.expression -> unit
val definition : Cursor.t -> Syntax.definition -> unit
