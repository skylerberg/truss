type t = {
  dependencies : Path.package -> Manifest.dependency list;
  interface : Interface.Lookups.t;
  core : Resolve.Names.key -> Core.t option;
  used_packages : Resolve.Names.key -> Path.package list;
}
