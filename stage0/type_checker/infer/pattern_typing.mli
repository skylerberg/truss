val check_binding_pattern :
  State.state ->
  State.env ->
  Syntax.pattern ->
  Types.ty ->
  is_var:bool ->
  mode:Language.Mode.t ->
  unit

val check_pattern :
  State.state -> State.env -> Syntax.pattern -> Types.ty -> mode:Language.Mode.t -> unit

val report_negated_unsigned : State.state -> Syntax.expression -> Types.ty -> Diagnostic.reported

val check_integer_literal :
  State.state -> State.env -> ?expected:Types.ty -> Syntax.expression -> Z.t -> Types.ty

val find_character_tag : State.state -> Syntax.string_literal -> Intrinsic.builtin option

val check_character_literal :
  State.state -> Syntax.id -> Syntax.string_literal -> Intrinsic.builtin -> Types.ty
