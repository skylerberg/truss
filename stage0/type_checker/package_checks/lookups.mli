type t = {
  interface : Interface.Lookups.t;
  core : Resolve.Names.key -> Core.t;
  used_packages : Resolve.Names.key -> Path.package list;
}
