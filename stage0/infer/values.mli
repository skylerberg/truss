module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower

val string_literal :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Syntax.string_literal ->
  Types.ty

val list_literal :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Syntax.expression list ->
  Types.ty

val map_literal :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  (Syntax.expression * Syntax.expression) list ->
  Types.ty

val lambda :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Syntax.pattern list ->
  Syntax.block ->
  Types.ty

val if_ :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Syntax.expression ->
  Syntax.block ->
  Syntax.else_branch option ->
  Types.ty

val match_ :
  State.state ->
  State.env ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Syntax.expression list ->
  Syntax.arm list ->
  Types.ty

val element_of_collection :
  State.state -> State.env -> quantifier:Syntax.expression -> Syntax.expression -> Types.ty
