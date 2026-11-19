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

val check_literal_fits : State.state -> Syntax.expression -> Z.t -> Types.ty -> unit
val find_character_tag : State.state -> Syntax.string_literal -> Language.Builtin_type.t option

val check_character_literal :
  State.state -> Syntax.id -> Syntax.string_literal -> Language.Builtin_type.t -> Types.ty
