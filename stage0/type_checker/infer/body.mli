module Names = Resolve.Names
module Environment = Interface.Environment
module Lower = Interface.Lower

type checked = { form : Core.t; tables : Tables.published; evidence_packages : Path.package list }

val check :
  Lookups.t -> Names.key -> checks_body:bool -> (checked, Syntax.diagnostic list) result option
