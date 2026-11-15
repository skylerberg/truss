type t = {
  interface : Interface.Lookups.t;
  core : Resolve.Names.key -> Core.t option;
  used_packages : Resolve.Names.key -> Path.package list;
}
