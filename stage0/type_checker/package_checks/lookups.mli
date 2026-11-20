type instantiation = { callee : Path.t; has_growing_arguments : bool }

type mentions = {
  paths : Path.t list;
  packages : Path.package list;
  instantiations : instantiation list;
}

type t = {
  interface : Interface.Lookups.t;
  read_core : Resolve.Names.key -> Core.t;
  read_mentions : Resolve.Names.key -> mentions;
}
