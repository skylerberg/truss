module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Properties = Interface.Properties
module Lower = Interface.Lower

val call :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Syntax.expression ->
  Syntax.argument list ->
  Types.ty
