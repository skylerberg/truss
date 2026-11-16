type t = {
  find_graph : Resolve.Names.key -> Mir.Graph.t option;
  list_places_without_own : Resolve.Names.key -> Core.origin list;
  interface : Interface.Lookups.t;
}
