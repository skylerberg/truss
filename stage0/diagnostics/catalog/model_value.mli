type t =
  | Integer of Z.t
  | Boolean of bool
  | Float of { value : float; is_single : bool }
  | Unit_value
  | Variant_value of { variant : string; fields : field list }
  | Record_value of { type_ : Types.ty; fields : field list }
  | Unknown

and field = { field : string; value : t }
