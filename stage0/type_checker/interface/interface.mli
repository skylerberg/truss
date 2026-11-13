(** Checking interfaces. *)

module Summary = Summary
module Lower = Lower
module Constants = Constants
module Environment = Environment
module Properties = Properties
module Impls = Impls
module Grants = Grants
module Check = Check

val diagnostics : Query.context -> Path.file -> Diagnostic.t list
(** Every interface error of a file, in its offsets and in order. *)
