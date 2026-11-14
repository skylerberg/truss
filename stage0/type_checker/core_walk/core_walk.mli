(** Traversal of the core form.

    A visitor is a record of callbacks. The [*_children] functions call the visitor on the direct
    children of one node, and do not recurse. {!deep} turns a visitor into one that recurses into
    every descendant. *)

type visit = {
  expression : Core.expression -> unit;
  statement : Core.statement -> unit;
  pattern : Core.pattern -> unit;
  callee : Core.callee -> unit;
      (** Called for every callee stored in a node other than a [Call]: an interpolated piece's
          [display], a cursor's [next], and a pattern's [equal]. The callee of a [Call] is not
          reported here, because the visitor sees the [Call] node itself. *)
  place : Core.place -> unit;  (** Called for every place, and for each place a [Field] is of. *)
}

val ignore_all : visit

val callees : (Core.callee -> unit) -> visit
(** A visitor that calls its argument on every callee: the callee of each [Call], and each callee
    stored in another node. *)

val place_type : Core.place -> Types.ty
val place_origin : Core.place -> Core.origin

val lent_places : Core.operand -> Core.place list
(** The places that a yielded operand lends: the operand itself if it is a place, and the fields of
    a yielded construct that are places, to any depth. *)

val place : visit -> Core.place -> unit
val operand : visit -> Core.operand -> unit
val block : visit -> Core.block -> unit
val loop_clause : visit -> Core.loop_clause -> unit
val expression_children : visit -> Core.expression -> unit
val statement_children : visit -> Core.statement -> unit
val pattern_children : visit -> Core.pattern -> unit

val deep : visit -> visit
(** A visitor that calls the given visitor on a node and then on all of its descendants, in
    evaluation order. *)

val expression : visit -> Core.expression -> unit
(** Calls the visitor on an expression and all of its descendants. *)

val definition : visit -> Core.definition -> unit
(** Calls the visitor on every node of a definition. *)

val block_exists :
  ?expression:(Core.expression -> bool) -> ?statement:(Core.statement -> bool) -> Core.block -> bool
(** Whether some expression or statement of a block, to any depth, satisfies its test. *)

val expression_exists :
  ?expression:(Core.expression -> bool) ->
  ?statement:(Core.statement -> bool) ->
  Core.expression ->
  bool
(** Whether an expression, or an expression or statement in it, satisfies its test. *)

val statement_exists :
  ?expression:(Core.expression -> bool) ->
  ?statement:(Core.statement -> bool) ->
  Core.statement ->
  bool
(** Whether a statement, or an expression or statement in it, satisfies its test. *)

(** How code can use [Tasks]. *)
type tasks_use =
  | Uses_tasks  (** It contains [concurrent] code, or a call in it uses [Tasks]. *)
  | Through_parameter
      (** A call in it uses a capability parameter, which may be instantiated with [Tasks]. *)
  | No_tasks

val tasks_use : ?solved:(int -> Types.capability_set) -> Core.block -> tasks_use
(** How code can use [Tasks]. [solved] gives the solution of a capability variable, for a core form
    whose capability variables are not solved yet. *)

val can_use_tasks : ?solved:(int -> Types.capability_set) -> Core.block -> bool
(** Whether code can use [Tasks]. An implementation that is provided [mut] around such code is a
    monitor. *)

val storage_index : Core.expression -> Core.place option
(** If an expression is an index of a [List], a [Slice], or an [Array], the collection it indexes.
    An element of one of these is a place; an index of any other collection is a call of the
    collection's [at], which lends the element. *)

val traverse_indirect : ('a -> 'b option) -> 'a Core.target -> 'b Core.target option
