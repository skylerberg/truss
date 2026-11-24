module Local_table : Hashtbl.S with type key = Core.local

type owned_scrutinee = { scrutinee : Core.local; written : Core.origin; is_part : bool }

module Type_table : Hashtbl.S with type key = Types.ty

type decided_type

type context = {
  lookups : Lookups.t;
  list_bounds : Interface.Impls.bounds;
  mode_keywords : (Syntax.id, Core.mode_keyword) Hashtbl.t;
  bare_names : (Syntax.id, string) Hashtbl.t Lazy.t;
  places_without_keyword : (Syntax.id, Language.Mode.t) Hashtbl.t;
  names : string Local_table.t;
  origins : Core.origin Local_table.t;
  binding_modes : Language.Mode.t Local_table.t;
  literal_views : unit Local_table.t;
  owned_scrutinees : owned_scrutinee Local_table.t;
  types : Types.ty Local_table.t;
  decided_types : decided_type Type_table.t;
  mutable parameters : Core.local list;
  implements_capability : bool;
  is_constant : bool;
  mutable mutable_locals : Core.local list;
  mutable diagnostics : Catalog.description list;
  mutable must_be_disjoint : (Core.id list * Core.id list) list;
}

val is_plain : context -> Types.ty -> bool
val is_view : context -> Types.ty -> bool
val holds_function : context -> Types.ty -> bool
val lends_nothing : context -> Types.ty -> bool
val stores_function : context -> Mir.callee -> int -> bool
val find_place_without_keyword : context -> Core.origin -> Language.Mode.t option
val report : context -> Catalog.Ownership.t -> unit
val classify_binding_mode : context -> Place.root -> Language.Mode.t
val views_literal : context -> Place.root -> bool
val find_root : context -> Place.root -> Catalog.Ownership.root
val find_owned_scrutinee : context -> Place.root -> Catalog.Ownership.scrutinee option
val find_place : context -> Place.t -> Catalog.Ownership.place
val collect : context -> Mir.Graph.t -> mode_keywords:Core.mode_keyword list -> unit
val find_copy : context -> Types.ty -> Core.origin -> Catalog.Ownership.copy option
val cover_with_mode_keyword : context -> Core.origin -> Core.origin Catalog.range
