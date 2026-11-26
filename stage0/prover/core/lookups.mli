type t = {
  interface : Interface.Lookups.t;
  mir : Mir.lookups;
  list_must_be_disjoint : Resolve.Names.key -> (Core.id list * Core.id list) list;
  list_recursion_group : Path.t -> Path.t list;
  may_abort : Path.t -> bool;
  list_proof_group : Path.t -> Path.t list;
}
