(** Visiting the expressions and statements of a tree.

    {!expression_parts} and {!statement_parts} visit one level: a node's own expressions, including
    those in the types and clauses it holds, with [expression], and the statements of the blocks it
    holds, with [statement]. A walk that needs a context overrides the nodes that change it and
    leaves every other to these, so a construct added to the tree is walked by every check without
    the check listing it. {!children} and {!statement} go all the way down through statements,
    calling one function on expressions. {!definition} calls it on each outermost expression of a
    definition. *)

val expression_parts :
  expression:(Syntax.expression -> unit) ->
  statement:(Syntax.statement -> unit) ->
  Syntax.expression ->
  unit

val statement_parts :
  expression:(Syntax.expression -> unit) ->
  statement:(Syntax.statement -> unit) ->
  Syntax.statement ->
  unit

val children : (Syntax.expression -> unit) -> Syntax.expression -> unit
val statement : (Syntax.expression -> unit) -> Syntax.statement -> unit
val type_expression : (Syntax.expression -> unit) -> Syntax.type_expression -> unit
val clause : (Syntax.expression -> unit) -> Syntax.clause -> unit
val loop_clause : (Syntax.expression -> unit) -> Syntax.loop_clause -> unit
val generic_parameter : (Syntax.expression -> unit) -> Syntax.generic_parameter -> unit
val definition_name : (Syntax.expression -> unit) -> Syntax.definition_name -> unit
val signature : (Syntax.expression -> unit) -> Syntax.signature -> unit

val definition :
  ?statement:(Syntax.statement -> unit) -> (Syntax.expression -> unit) -> Syntax.definition -> unit
(** Calls the function on each outermost expression of a definition. With [~statement], each
    statement of the definition's own blocks goes to it instead, so a walk that cares about
    statements sees every one. *)

val spans : Syntax.definition -> Syntax.span array
(** The span of each expression, statement, pattern, match arm, record update, contract clause, and
    loop clause of a definition, indexed by node id. The core form holds no spans, so a stage that
    reads it looks up a node's origin here to show its source text. *)

val names : Syntax.definition -> Syntax.name list
(** Every name in a definition, references and the names that bind, in source order. Tools use it to
    find the name at a position, and checks to find every binding. *)
