type t = {
  interface : Interface.Lookups.t;
  read_resolved : Resolve.Names.key -> Resolve.resolved;
  read_tables : Resolve.Names.key -> Infer.tables;
  find_capability_uses : Resolve.Names.key -> Infer.capability_use list option;
  list_recursion_group : Path.t -> Path.t list;
}
