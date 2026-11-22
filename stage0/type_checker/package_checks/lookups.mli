type t = {
  interface : Interface.Lookups.t;
  read_core : Resolve.Names.key -> Core.t;
  list_uses : Path.package -> (Resolve.Names.key * Path.t) list;
  list_instantiations : Path.package -> (Path.t * Path.t * bool) list;
  list_used_packages : Path.package -> Path.package list;
}
