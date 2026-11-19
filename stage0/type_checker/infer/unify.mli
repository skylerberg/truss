type t = {
  mutable next : int;
  type_solutions : (int, Types.ty) Hashtbl.t;
  value_solutions : (int, Types.value) Hashtbl.t;
  mutable capability_variable_count : int;
  mutable deferred_capability_equalities : (Types.capability_set * Types.capability_set) list;
  mutable frozen : int list;
  domains : (int, Scalar_set.t) Hashtbl.t;
  mutable list_rigid_members : Types.ty -> Scalar_set.t option;
  levels : (int, int) Hashtbl.t;
  mutable level : int;
}

val create : unit -> t
val make_fresh_type : t -> Types.ty
val make_fresh_number : t -> Scalar_set.t -> Types.ty
val make_fresh_value : t -> Types.value
val make_fresh_capability_variable : t -> Types.capability_set
val resolve : t -> Types.ty -> Types.ty
val resolve_value : t -> Types.value -> Types.value
val zonk : t -> Types.ty -> Types.ty
val zonk_trait : t -> Types.trait_reference -> Types.trait_reference
val read_domain : t -> int -> Scalar_set.t
val list_possible_members : t -> Types.ty -> Scalar_set.t option
val narrow : t -> int -> Scalar_set.t -> bool

type unknown = Unknown_type of int | Unknown_number of int | Unknown_value of int

val list_unknowns : t -> Types.ty -> unknown list
val read_unknown_index : unknown -> int
val read_level : t -> int -> int
val lower : t -> level:int -> Types.ty -> unit
val lower_to : t -> level:int -> int -> unit
val find_lowest_level : t -> unknown list -> int option
val list_argument_unknowns : t -> Types.argument -> unknown list
val unify : t -> Types.ty -> Types.ty -> bool
val unify_arguments : t -> Types.argument list -> Types.argument list -> bool
val unify_value : t -> Types.value -> Types.value -> bool
