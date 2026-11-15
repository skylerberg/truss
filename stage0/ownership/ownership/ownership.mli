type result = {
  diagnostics : Syntax.diagnostic list;
  must_be_disjoint : (Core.origin * Core.origin) list;
}

val ownership : (Resolve.Names.key, result option) Query.query
val diagnostics : Query.context -> Path.file -> Diagnostic.t list
