type capability_use = Capabilities.capability_use = {
  capabilities : Types.capability_set;
  callee : Path.t option;
}

type checked = {
  form : Core.t;
  tables : Tables.published;
  used_packages : Path.package list;
  places_without_keyword : (Syntax.id * Language.Mode.t) list;
  mode_keywords : Core.mode_keyword list;
  capability_uses : capability_use list;
}

val check :
  Lookups.t -> Resolve.Names.key -> checks_body:bool -> (checked, Catalog.diagnostic list) result
