type value = Constant_value.t =
  | Integer of Z.t
  | Boolean of bool
  | Text of string
  | Constructed of { type_ : Path.t; variant : string option; fields : (string * value) list }

type outcome = Constant_value.outcome =
  | Known of value
  | Calls_function
  | Depends_on_itself
  | Unevaluated

type integer = { bits : int; is_signed : bool }

val evaluate_expression :
  Lookups.t ->
  Resolve.resolved ->
  integer:integer option ->
  Syntax.expression ->
  Constant_value.outcome

val evaluate_constant : Lookups.t -> Path.t -> Constant_value.outcome

type count = Count of Z.t | Invalid_count of Catalog.Typing.count_error | Unevaluated_count

val evaluate_count : Lookups.t -> Path.t -> count
