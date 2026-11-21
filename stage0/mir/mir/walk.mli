val list_nested_blocks : Tree.statement -> Tree.block list
val iter_code : (Tree.statement -> unit) -> Tree.t -> unit
val iter_formula : (Tree.statement -> unit) -> Tree.formula -> unit
val find_callee : Tree.statement -> Tree.callee option
val is_in_sequence : Tree.place -> bool
val extract_operand_type : Tree.operand -> Types.ty
