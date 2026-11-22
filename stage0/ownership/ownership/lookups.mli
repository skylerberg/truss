type t = {
  find_code : Resolve.Names.key -> Mir.code option;
  list_places_without_keyword : Resolve.Names.key -> (Syntax.id * Language.Mode.t) list;
  list_mode_keywords : Resolve.Names.key -> Core.mode_keyword list;
  interface : Interface.Lookups.t;
}
