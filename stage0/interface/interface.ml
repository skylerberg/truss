module Summary = Summary
module Lower = Lower
module Constants = Constants
module Environment = Environment
module Properties = Properties
module Impls = Impls
module Grants = Grants
module Check = Check

let diagnostics database module_ =
  Resolve.Names.per_definition database module_ (Query.demand database Check.diagnostics)
