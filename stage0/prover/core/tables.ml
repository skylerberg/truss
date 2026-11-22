type stated =
  | In_range of Logic.symbol
  | Field_in_range of Logic.term
  | Value_of of Logic.symbol
  | Contract_of of Logic.symbol
  | Limited_link of Logic.symbol
  | Exclusive of Logic.symbol
  | Array_length of Logic.symbol
  | Ranked_model of Logic.symbol
  | Ranked_elements of Types.ty
  | Range_elements of Types.ty
  | Non_negative_rank of Types.ty

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

module Local_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Locals.local
end))

module Stated_table = Hashtbl.Make (Structural_key.Make (struct
  type t = stated
end))

module Model_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Types.ty * Types.ty
end))

module Axiom_clause_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Logic.symbol * string * Core.origin
end))
