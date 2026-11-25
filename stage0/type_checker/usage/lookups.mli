type t = {
  interface : Interface.Lookups.t;
  read_resolved : Resolve.Names.key -> Resolve.resolved;
  read_tables : Resolve.Names.key -> Infer.tables;
  uses_run_forever : Resolve.Names.key -> bool;
  is_recursive : Path.t -> bool;
}
