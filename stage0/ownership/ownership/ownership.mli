module Lookups = Lookups

type result = {
  diagnostics : Catalog.diagnostic list;
  must_be_disjoint : (Core.id list * Core.id list) list;
}

val check : Lookups.t -> Resolve.Names.key -> result
