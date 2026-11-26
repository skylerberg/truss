type stated =
  | In_range of Logic.symbol
  | Field_in_range of Logic.term
  | Value_of of Logic.symbol
  | Contract_of of Logic.symbol
  | Limited_link of Logic.symbol
  | Array_length of Logic.symbol
  | Ranked_model of Logic.symbol
  | Ranked_elements of Types.ty
  | Range_elements of Types.ty
  | Method_cost_bound of Logic.symbol
  | Laws_of of Types.trait_reference * Types.ty
  | Derived_equality of Logic.term
  | Potential_of of Logic.term

module Symbol_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Logic.symbol
end))

module Term_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Logic.term
end))

module Type_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Types.ty
end))

module Path_table = Hashtbl.Make (Path)

module Stated_table = Hashtbl.Make (Structural_key.Make (struct
  type t = stated
end))
