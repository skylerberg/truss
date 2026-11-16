module Names = Resolve.Names
module Environment = Interface.Environment
module Elaborate = Interface.Elaborate

type checked = { form : Core.t; tables : Tables.published; evidence_packages : Path.package list }

val check :
  Lookups.t -> Names.key -> checks_body:bool -> (checked, Diagnostic.in_definition list) result
