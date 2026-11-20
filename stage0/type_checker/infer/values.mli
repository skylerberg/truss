val check_string_literal :
  State.state -> State.env -> ?expected:Types.ty -> Syntax.string_literal -> Types.ty

val check_list_literal :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Syntax.expression list ->
  Types.ty

val check_map_literal :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  (Syntax.expression * Syntax.expression) list ->
  Types.ty

val check_lambda :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Syntax.pattern list ->
  Syntax.block ->
  Types.ty

val check_if :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Syntax.block ->
  Syntax.else_branch option ->
  Types.ty

val match_ :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression list ->
  Syntax.arm list ->
  Types.ty

val check_collection_element :
  State.state -> State.env -> quantifier:Syntax.expression -> Syntax.expression -> Types.ty
