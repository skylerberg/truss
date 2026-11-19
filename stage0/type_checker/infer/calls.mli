val check_arguments_alone : State.state -> State.env -> Syntax.argument list -> Types.ty -> Types.ty

val check_function_value_call :
  State.state ->
  State.env ->
  Syntax.expression ->
  Syntax.expression ->
  Syntax.argument list ->
  Types.ty

val check_argument :
  State.state ->
  State.env ->
  Syntax.expression ->
  Types.parameter_info ->
  has_generic_type:bool ->
  Language.Mode.t

val check_arguments :
  State.state ->
  State.env ->
  ?constructor:string ->
  Syntax.expression ->
  Types.parameter_info list ->
  declared:Types.parameter_info list ->
  Syntax.argument list ->
  has_receiver:bool ->
  (Tables.argument list * string list, Types.ty) result

val check_named_call :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Path.t ->
  Types.signature ->
  type_arguments:Syntax.bracket_item list ->
  Syntax.argument list ->
  Types.ty

val check_record_update :
  State.state ->
  State.env ->
  Syntax.expression ->
  Syntax.expression ->
  Syntax.update list ->
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
