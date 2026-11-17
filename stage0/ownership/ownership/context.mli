module Local_table : Hashtbl.S with type key = Core.local

type context = {
  lookups : Lookups.t;
  list_bounds : Types.parameter -> Types.trait_reference list;
  spans : Source.Definition_span.t array Lazy.t;
  text : string Lazy.t;
  mode_keywords : (Core.origin, Core.mode_keyword) Hashtbl.t;
  places_without_keyword : (Core.origin, Types.mode) Hashtbl.t;
  names : string Local_table.t;
  origins : Core.origin Local_table.t;
  binding_modes : Types.mode Local_table.t;
  types : Types.ty Local_table.t;
  mutable parameters : Core.local list;
  implements_capability : bool;
  mutable mutable_locals : Core.local list;
  mutable diagnostics : Diagnostic.in_definition list;
  mutable must_be_disjoint : (Core.origin * Core.origin) list;
}

val is_plain : context -> Types.ty -> bool
val is_copyable : context -> Types.ty -> bool
val is_view : context -> Types.ty -> bool
val holds_function : context -> Types.ty -> bool
val lends_nothing : context -> Types.ty -> bool
val stores_function : context -> Mir.callee -> int -> bool
val locate_origin : context -> Core.origin -> Source.Definition_span.t

val report :
  context ->
  ?fixes:Source.Definition_span.t Diagnostic.fix list ->
  ?notes:(Source.Definition_span.t * string) list ->
  Diagnostic.Code.ownership ->
  Source.Definition_span.t ->
  string ->
  unit

val classify_binding_mode : context -> Place.root -> Types.mode
val show_root : context -> Place.root -> string
val show : context -> Place.t -> string
val collect : context -> Mir.Graph.t -> mode_keywords:Core.mode_keyword list -> unit

val copy_fix :
  context -> string -> Types.ty -> Core.origin -> Source.Definition_span.t Diagnostic.fix list

val locate_with_mode_keyword : context -> Core.origin -> Source.Definition_span.t
