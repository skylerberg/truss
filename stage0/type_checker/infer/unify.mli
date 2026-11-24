type mode = { context : Interface.Elaborator.t; checks_specification : bool }

type t = {
  mutable next : int;
  type_solutions : (int, Types.ty) Hashtbl.t;
  value_solutions : (int, Types.value) Hashtbl.t;
  mutable capability_variable_count : int;
  mutable deferred_capability_equalities : (Types.capability_set * Types.capability_set) list;
  domains : (int, Language.Builtin_type.t list) Hashtbl.t;
  list_rigid_members : Interface.Elaborator.t -> Types.ty -> Language.Builtin_type.t list;
  mutable mode : mode;
  specification_unknowns : (int, unit) Hashtbl.t;
  mutable refused_code_unknown : int option;
  mutable decided_numbers : int list;
}

val create :
  context:Interface.Elaborator.t ->
  list_rigid_members:(Interface.Elaborator.t -> Types.ty -> Language.Builtin_type.t list) ->
  t

val make_fresh_type : t -> Types.ty
val make_fresh_number : t -> Language.Builtin_type.t list -> Types.ty
val make_fresh_value : t -> Types.value
val make_fresh_argument : t -> Types.generic -> Types.argument
val make_fresh_capability_variable : t -> Types.capability_set
val resolve : t -> Types.ty -> Types.ty
val read_root : t -> int -> int
val resolve_value : t -> Types.value -> Types.value
val zonk : t -> Types.ty -> Types.ty
val zonk_trait : t -> Types.trait_reference -> Types.trait_reference
val find_domain : t -> int -> Language.Builtin_type.t list option
val list_possible_members : t -> Types.ty -> Language.Builtin_type.t list
val is_within : t -> Types.ty -> Language.Builtin_type.t list -> bool
val may_decide : t -> int -> bool
val count_solutions : t -> int
val poison : t -> int -> Diagnostic.reported -> unit

type unknown = Unknown_type of int | Unknown_value of int

val list_unknowns : t -> Types.ty -> unknown list
val list_argument_unknowns : t -> Types.argument -> unknown list
val unify : ?modulo_views:bool -> t -> Types.ty -> Types.ty -> bool
val unify_arguments : ?modulo_views:bool -> t -> Types.argument list -> Types.argument list -> bool
val unify_value : t -> Types.value -> Types.value -> bool
