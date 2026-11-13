module Summary = Summary
module Lower = Lower
module Constants = Constants
module Environment = Environment
module Properties = Properties
module Impls = Impls
module Grants = Grants
module Check = Check

let diagnostics database file =
  Resolve.Names.per_definition database file (Query.demand database Check.diagnostics)
