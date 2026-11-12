module T = Types

type t = {
  mutable next : int;
  types : (int, T.ty) Hashtbl.t;
  values : (int, T.value) Hashtbl.t;
  mutable capability_variable_count : int;
  mutable deferred_capability_equalities : (T.capability list * T.capability list) list;
  mutable integer_range : T.ty -> (Z.t * Z.t) option;
}

val create : unit -> t
val fresh : t -> T.ty
val fresh_literal : t -> T.literal_kind -> T.ty
val fresh_value : t -> T.value
val fresh_capability_variable : t -> T.capability list
val resolve : t -> T.ty -> T.ty
val resolve_value : t -> T.value -> T.value
val zonk : t -> T.ty -> T.ty
val zonk_trait : t -> T.trait_reference -> T.trait_reference
val literal_fits : t -> T.literal_kind -> T.ty -> bool

type unknown =
  | Unknown_type of int
  | Unknown_literal of T.literal_kind * int
  | Unknown_value of int

val unknowns : t -> T.ty -> unknown list
val argument_unknowns : t -> T.argument -> unknown list
val unify : t -> T.ty -> T.ty -> bool
val unify_arguments : t -> T.argument list -> T.argument list -> bool
val unify_value : t -> T.value -> T.value -> bool
