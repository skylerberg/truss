module T = Types
module C = Tables
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower

val arguments_alone :
  State.state -> State.env -> Syntax.argument list -> Lookups.T.ty -> Lookups.T.ty

val function_value_call :
  State.state ->
  State.env ->
  Syntax.expression ->
  Syntax.expression ->
  Syntax.argument list ->
  State.T.ty

val check_argument :
  State.state -> State.env -> Syntax.expression -> Lookups.T.parameter_info -> Lookups.T.mode

val match_arguments :
  State.state ->
  Syntax.expression ->
  Lookups.T.parameter_info list ->
  Syntax.argument list ->
  record:bool ->
  (Syntax.argument * int) list * string list

val check_arguments :
  State.state ->
  State.env ->
  Lookups.T.parameter_info list ->
  (Syntax.argument * int) list ->
  offset:int ->
  State.C.argument list

val named_call :
  State.state ->
  State.env ->
  ?expected:Unify.T.ty ->
  Syntax.expression ->
  Path.t ->
  Lookups.T.signature ->
  type_arguments:Syntax.bracket_item list ->
  Syntax.argument list ->
  State.T.ty

val construct :
  State.state ->
  State.env ->
  ?expected:Unify.T.ty ->
  ?type_arguments:Members.T.argument list ->
  Syntax.expression ->
  Path.t ->
  string option ->
  Syntax.argument list ->
  Lookups.T.ty
