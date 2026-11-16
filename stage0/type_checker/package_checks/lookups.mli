type t = {
  interface : Interface.Lookups.t;
  read_core : Resolve.Names.key -> Core.t;
  list_used_packages : Resolve.Names.key -> Path.package list;
}
