type stated =
  | In_range of Logic.symbol
  | Value_of of Logic.symbol
  | Contract_of of Logic.symbol
  | Limited_link of Logic.symbol
  | Exclusive of Logic.symbol
  | Array_length of Logic.symbol
  | Ranked_model of Logic.symbol
  | Ranked_elements of Types.ty

module Symbol_table : Hashtbl.S with type key = Logic.symbol
module Term_table : Hashtbl.S with type key = Logic.term
module Type_table : Hashtbl.S with type key = Types.ty
module Local_table : Hashtbl.S with type key = Locals.local
module Stated_table : Hashtbl.S with type key = stated
module Model_table : Hashtbl.S with type key = Types.ty * Types.ty
module Axiom_clause_table : Hashtbl.S with type key = Logic.symbol * string * Core.origin
