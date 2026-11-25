type t = {
  interface : Interface.Lookups.t;
  list_tests : Path.package -> string -> Resolve.Names.key list;
  list_instantiations : Resolve.Names.key -> (Resolve.Names.key * bool) list;
  list_users : Path.t -> Resolve.Names.declaration Seq.t;
  list_used : Resolve.Names.key -> Resolve.Names.declaration list;
  was_unused : Path.t -> bool;
  is_package_used : by:Path.package -> Path.package -> bool;
}
