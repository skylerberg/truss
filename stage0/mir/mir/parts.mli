type code = { tree : Tree.t; graph : Graph.t }
type body_part = Body of code | Initializer of code | No_code

type contract_part = {
  contract : Tree.contract option;
  defaults : Tree.t Tree.defaults option;
  default_graphs : Graph.t Tree.defaults option;
  laws : Tree.law list;
  type_clauses : Tree.type_clauses option;
}

type lookups = {
  form_origin : Path.t -> (Infer.form_origin * Types.substitution) option;
  body_part : Resolve.Names.key -> body_part;
  contract_part : Resolve.Names.key -> contract_part;
  generated_parts : Path.t -> body_part * contract_part;
}

type 'form sourced = { source : Resolve.Names.key; form : 'form }

val code : body_part -> Tree.t option
val graph : body_part -> Graph.t option
val body_part_of_path : lookups -> Path.t -> body_part sourced option
val code_of_path : lookups -> Path.t -> Tree.t sourced option
val graph_of_path : lookups -> Path.t -> Graph.t sourced option
val initializer_of_path : lookups -> Path.t -> Tree.t sourced option
val initializer_graph_of_path : lookups -> Path.t -> Graph.t sourced option
val contract_of_path : lookups -> Path.t -> Tree.contract sourced option
val defaults_of_path : lookups -> Path.t -> Tree.t Tree.defaults sourced option
val default_graphs_of_path : lookups -> Path.t -> Graph.t Tree.defaults sourced option
val type_clauses_of_path : lookups -> Path.t -> Tree.type_clauses sourced option
