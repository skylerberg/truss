module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower

val arguments_alone : State.state -> State.env -> Syntax.argument list -> Types.ty -> Types.ty

val function_value_call :
  State.state ->
  State.env ->
  Syntax.expression ->
  Syntax.expression ->
  Syntax.argument list ->
  Types.ty

val check_argument :
  State.state -> State.env -> Syntax.expression -> Types.parameter_info -> Types.mode

val match_arguments :
  State.state ->
  Syntax.expression ->
  Types.parameter_info list ->
  Syntax.argument list ->
  record:bool ->
  (Syntax.argument * int) list * string list

val check_arguments :
  State.state ->
  State.env ->
  Types.parameter_info list ->
  (Syntax.argument * int) list ->
  offset:int ->
  Tables.argument list

val named_call :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Path.t ->
  Types.signature ->
  type_arguments:Syntax.bracket_item list ->
  Syntax.argument list ->
  Types.ty

val construct :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  ?type_arguments:Types.argument list ->
  Syntax.expression ->
  Path.t ->
  string option ->
  Syntax.argument list ->
  Types.ty
