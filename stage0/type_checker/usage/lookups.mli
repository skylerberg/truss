type t = {
  names : Resolve.Names.lookups;
  read_resolved : Resolve.Names.key -> Resolve.resolved;
  read_tables : Resolve.Names.key -> Infer.tables;
}
