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

module Symbol_table : Hashtbl.S with type key = Logic.symbol
module Term_table : Hashtbl.S with type key = Logic.term
module Type_table : Hashtbl.S with type key = Types.ty
module Path_table : Hashtbl.S with type key = Path.t
module Stated_table : Hashtbl.S with type key = stated
