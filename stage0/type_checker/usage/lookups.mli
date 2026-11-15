type t = {
  names : Resolve.Names.lookups;
  resolved : Resolve.section -> Resolve.Names.key -> Resolve.resolved option;
  tables : Resolve.Names.key -> Infer.tables option;
}
