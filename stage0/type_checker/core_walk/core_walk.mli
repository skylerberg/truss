type visit = {
  expression : Core.expression -> unit;
  statement : Core.statement -> unit;
  pattern : Core.pattern -> unit;
  callee : Core.callee -> unit;
  place : Core.place -> unit;
}

val ignore_all : visit
val callees : (Core.callee -> unit) -> visit
val place_type : Core.place -> Types.ty
val place_origin : Core.place -> Core.origin
val place : visit -> Core.place -> unit
val operand : visit -> Core.operand -> unit
val block : visit -> Core.block -> unit
val loop_clause : visit -> Core.loop_clause -> unit
val expression_children : visit -> Core.expression -> unit
val statement_children : visit -> Core.statement -> unit
val pattern_children : visit -> Core.pattern -> unit
val deep : visit -> visit
val expression : visit -> Core.expression -> unit
val definition : visit -> Core.definition -> unit
val local_names : Core.definition -> (Core.local, string) Hashtbl.t

val expression_exists :
  ?expression:(Core.expression -> bool) ->
  ?statement:(Core.statement -> bool) ->
  Core.expression ->
  bool

type tasks_use = Uses_tasks | Through_parameter | No_tasks

val tasks_use : ?solved:(int -> Types.capability_set) -> Core.block -> tasks_use
val can_use_tasks : ?solved:(int -> Types.capability_set) -> Core.block -> bool
val traverse_indirect : ('a -> 'b option) -> 'a Core.target -> 'b Core.target option
