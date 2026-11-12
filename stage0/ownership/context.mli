module T = Types

type kind = Owned | Borrowed | Borrowed_mut

type context = {
  database : Query.context;
  bounds : T.parameter -> T.trait_reference list;
  spans : Syntax.span array;
  marks : (Core.origin * Syntax_walk.mark) list;
  names : (Core.local, string) Hashtbl.t;
  kinds : (Core.local, kind) Hashtbl.t;
  types : (Core.local, T.ty) Hashtbl.t;
  mutable parameters : Core.local list;
  yields : bool;
  implements_capability : bool;
  mutable mutable_locals : Core.local list;
  mutable diagnostics : Syntax.diagnostic list;
  mutable moves : Core.id list;
  mutable must_be_disjoint : (Core.origin * Core.origin) list;
}

val plain : context -> Types.ty -> bool
val copyable : context -> Types.ty -> bool
val is_view : context -> Types.ty -> bool
val holds_function : context -> Types.ty -> bool
val stores_function : context -> Core.callee -> int -> bool
val span : context -> Core.origin -> Syntax.span

val report :
  context ->
  ?fixes:Syntax.span Diagnostic.fix list ->
  ?notes:(Syntax.span * string) list ->
  Diagnostic.Code.ownership ->
  Syntax.span ->
  string ->
  unit

val kind : context -> Place.root -> kind
val show_root : context -> Place.root -> string
val show : context -> Place.t -> string
val collect : context -> Core.definition -> unit
val copy_at : context -> Core.origin -> Syntax.span Diagnostic.edit list
val with_mark : context -> Core.origin -> Syntax.span
