type visit = {
  expression : Core.expression -> unit;
  statement : Core.statement -> unit;
  pattern : Core.pattern -> unit;
  callee : Core.callee -> unit;
  place : Core.place -> unit;
}

val ignore_all : visit
val compute_place_type : Core.place -> Types.ty
val compute_place_origin : Core.place -> Core.origin
val walk_operand : visit -> Core.operand -> unit
val walk_block : visit -> Core.block -> unit
val walk_loop_clause : visit -> Core.loop_clause -> unit
val walk_expression_children : visit -> Core.expression -> unit
val walk_iteration : visit -> Core.iteration -> unit
val walk_statement_children : visit -> Core.statement -> unit
val walk_pattern_children : visit -> Core.pattern -> unit
val make_deep_visitor : visit -> visit
val walk_expression : visit -> Core.expression -> unit
val walk_definition : visit -> Core.definition -> unit
val is_functional : (visit -> unit) -> bool
val states_measure : Core.loop_clause list -> bool
val has_implicit_measure : Core.expression -> bool

type tasks_use = Uses_tasks | Through_parameter | No_tasks

val compute_tasks_use : ?read_solved:(int -> Types.capability_set) -> Core.block -> tasks_use
val can_use_tasks : Core.block -> bool
val traverse_indirect : ('a -> 'b option) -> 'a Core.target -> 'b Core.target option
val find_local_name : Core.local -> string option
