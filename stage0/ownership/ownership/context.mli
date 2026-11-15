type context = {
  lookups : Lookups.t;
  bounds : Types.parameter -> Types.trait_reference list;
  spans : Source.Definition_span.t array Lazy.t;
  mode_keywords : (Core.origin, Types.mode * Core.mode_keyword) Hashtbl.t;
  names : (Core.local, string) Hashtbl.t;
  binding_modes : (Core.local, Types.mode) Hashtbl.t;
  types : (Core.local, Types.ty) Hashtbl.t;
  mutable parameters : Core.local list;
  implements_capability : bool;
  mutable mutable_locals : Core.local list;
  mutable diagnostics : Diagnostic.in_definition list;
  mutable must_be_disjoint : (Core.origin * Core.origin) list;
}

val plain : context -> Types.ty -> bool
val copyable : context -> Types.ty -> bool
val is_view : context -> Types.ty -> bool
val holds_function : context -> Types.ty -> bool
val stores_function : context -> Mir.callee -> int -> bool
val span : context -> Core.origin -> Source.Definition_span.t

val report :
  context ->
  ?fixes:Source.Definition_span.t Diagnostic.fix list ->
  ?notes:(Source.Definition_span.t * string) list ->
  Diagnostic.Code.ownership ->
  Source.Definition_span.t ->
  string ->
  unit

val binding_mode : context -> Place.root -> Types.mode
val show_root : context -> Place.root -> string
val show : context -> Place.t -> string
val collect : context -> Mir.Graph.t -> unit
val copy_edits : context -> Core.origin -> Source.Definition_span.t Diagnostic.edit list
val span_with_mode_keyword : context -> Core.origin -> Source.Definition_span.t
