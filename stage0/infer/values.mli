module T = Types
module C = Tables
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower

val string_literal :
  State.state ->
  State.env ->
  ?expected:Unify.T.ty ->
  Syntax.expression ->
  Syntax.string_literal ->
  State.T.ty

val list_literal :
  State.state ->
  State.env ->
  ?expected:Unify.T.ty ->
  Syntax.expression ->
  Syntax.expression list ->
  Statements.T.ty

val map_literal :
  State.state ->
  State.env ->
  ?expected:Unify.T.ty ->
  Syntax.expression ->
  (Syntax.expression * Syntax.expression) list ->
  Statements.T.ty

val lambda :
  State.state ->
  State.env ->
  ?expected:Unify.T.ty ->
  Syntax.expression ->
  Syntax.pattern list ->
  Syntax.block ->
  Statements.T.ty

val if_ :
  State.state ->
  State.env ->
  ?expected:State.T.ty ->
  Syntax.expression ->
  Syntax.expression ->
  Syntax.block ->
  Syntax.else_branch option ->
  Statements.T.ty

val match_ :
  State.state ->
  State.env ->
  ?expected:State.T.ty ->
  Syntax.expression ->
  Syntax.expression list ->
  Syntax.arm list ->
  Statements.T.ty

val element_of_collection :
  State.state -> State.env -> quantifier:Syntax.expression -> Syntax.expression -> Statements.T.ty
