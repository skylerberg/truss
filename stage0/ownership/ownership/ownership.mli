module Lookups = Lookups

type result = {
  diagnostics : Diagnostic.in_definition list;
  must_be_disjoint : (Core.origin list * Core.origin list) list;
}

val check : Lookups.t -> Resolve.Names.key -> result
