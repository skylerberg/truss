type t = {
  source : Path.file -> Source.t;
  interface : Interface.Lookups.t;
  mir : Mir.lookups;
  patterns : Resolve.Names.key -> unit;
  must_be_disjoint : Resolve.Names.key -> (Core.origin * Core.origin) list;
  recursion_group : Path.t -> Path.t list;
}
