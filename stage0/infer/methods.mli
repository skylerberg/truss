module T = Types
module C = Tables
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Properties = Interface.Properties
module Lower = Interface.Lower

val call :
  State.state ->
  State.env ->
  ?expected:State.T.ty ->
  Syntax.expression ->
  Syntax.expression ->
  Syntax.argument list ->
  Calls.T.ty
