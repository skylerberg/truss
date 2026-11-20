type checked = {
  form : Core.t;
  tables : Tables.published;
  used_packages : Path.package list;
  places_without_keyword : (Syntax.id * Language.Mode.t) list;
  mode_keywords : Core.mode_keyword list;
  requires_run_forever : bool;
}

val check :
  Lookups.t ->
  Resolve.Names.key ->
  checks_body:bool ->
  (checked, Diagnostic.in_definition list) result
