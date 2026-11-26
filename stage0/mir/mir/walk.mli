val list_nested_blocks : Tree.statement -> Tree.block list
val iter_code : (Tree.statement -> unit) -> Tree.t -> unit
val iter_run_code : (Tree.statement -> unit) -> Tree.t -> unit
val iter_formula : (Tree.statement -> unit) -> Tree.formula -> unit
val iter_places : (Core.origin -> Tree.place -> unit) -> Tree.t -> unit
val iter_formula_places : (Core.origin -> Tree.place -> unit) -> Tree.formula -> unit
val iter_locals : (Tree.local_info -> unit) -> Tree.t -> unit
val iter_formula_locals : (Tree.local_info -> unit) -> Tree.formula -> unit
val list_evaluated_asserts : Tree.t -> (int * Tree.t) list
val list_leading_fields : Tree.projection list -> string list
val list_mut_provided_places : Tree.provided list -> Tree.place list

type changed = { origin : Core.origin; place : Tree.place; is_elements : bool }

val classify_changed_part : changed -> string list * bool

val list_changed_places :
  list_modified:(Tree.callee -> int -> Types.modified list option) ->
  Tree.block list ->
  changed list

val find_callee : Tree.statement -> Tree.callee option
val is_in_sequence : Tree.place -> bool
val extract_operand_type : Tree.operand -> Types.ty
