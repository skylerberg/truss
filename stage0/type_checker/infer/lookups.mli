type t = {
  interface : Interface.Lookups.t;
  read_contract : Resolve.Names.key -> Core.t;
  read_clause_text : Resolve.Names.key -> Core.origin -> string;
}
