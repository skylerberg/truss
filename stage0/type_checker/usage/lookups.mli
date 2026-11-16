type t = {
  names : Resolve.Names.lookups;
  resolved : Resolve.Names.key -> Resolve.resolved;
  tables : Resolve.Names.key -> Infer.tables;
}
