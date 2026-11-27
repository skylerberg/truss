type t = {
  interface : Interface.Lookups.t;
  read_resolved : Resolve.Names.key -> Resolve.resolved;
  read_tables : Resolve.Names.key -> Infer.tables;
  read_capability_uses : Resolve.Names.key -> Types.capability_set;
}
