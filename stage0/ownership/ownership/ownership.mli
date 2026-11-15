module Lookups = Lookups

type result = {
  diagnostics : Syntax.diagnostic list;
  must_be_disjoint : (Core.origin * Core.origin) list;
}

val check : Lookups.t -> Resolve.Names.key -> result option
