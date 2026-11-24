val list_nested_blocks : Tree.statement -> Tree.block list
val iter_code : (Tree.statement -> unit) -> Tree.t -> unit
val iter_formula : (Tree.statement -> unit) -> Tree.formula -> unit
val iter_places : (Core.origin -> Tree.place -> unit) -> Tree.t -> unit
val iter_formula_places : (Core.origin -> Tree.place -> unit) -> Tree.formula -> unit
val list_evaluated_asserts : Tree.t -> (int * Tree.t) list
val list_leading_fields : Tree.projection list -> string list
val list_mut_provided_places : Tree.provided list -> Tree.place list

val list_changed_places :
  list_modified:(Tree.callee -> int -> string list list option) ->
  Tree.block list ->
  (Core.origin * Tree.place) list

val find_callee : Tree.statement -> Tree.callee option
val is_in_sequence : Tree.place -> bool
val extract_operand_type : Tree.operand -> Types.ty
