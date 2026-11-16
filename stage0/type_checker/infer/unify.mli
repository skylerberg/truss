type t = {
  mutable next : int;
  type_solutions : (int, Types.ty) Hashtbl.t;
  value_solutions : (int, Types.value) Hashtbl.t;
  mutable capability_variable_count : int;
  mutable deferred_capability_equalities : (Types.capability_set * Types.capability_set) list;
  mutable find_integer_range : Types.ty -> (Z.t * Z.t) option;
  code_literals : (int, unit) Hashtbl.t;
}

val create : unit -> t
val make_fresh_type : t -> Types.ty
val make_fresh_literal : t -> Types.literal_kind -> Types.ty
val make_fresh_value : t -> Types.value
val make_fresh_capability_variable : t -> Types.capability_set
val resolve : t -> Types.ty -> Types.ty
val resolve_value : t -> Types.value -> Types.value
val zonk : t -> Types.ty -> Types.ty
val zonk_trait : t -> Types.trait_reference -> Types.trait_reference
val literal_fits : t -> Types.literal_kind -> Types.ty -> bool

type unknown =
  | Unknown_type of int
  | Unknown_literal of Types.literal_kind * int
  | Unknown_value of int

val list_unknowns : t -> Types.ty -> unknown list
val list_argument_unknowns : t -> Types.argument -> unknown list
val unify : t -> Types.ty -> Types.ty -> bool
val unify_arguments : t -> Types.argument list -> Types.argument list -> bool
val unify_value : t -> Types.value -> Types.value -> bool
