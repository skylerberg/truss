module Names = Resolve.Names
module Environment = Interface.Environment
module Lower = Interface.Lower

type type_check_result = {
  tables : Tables.published;
  core : Core.t option;
  diagnostics : Syntax.diagnostic list;
  evidence : Path.package list;
}

val type_check_result : (Expressions.Names.key, type_check_result option) Query.query
val diagnostics : Query.context -> Path.file -> Diagnostic.t list
