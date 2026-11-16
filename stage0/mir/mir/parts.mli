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
  find_form_origin : Path.t -> (Infer.form_origin * Types.substitution) option;
  read_body_part : Resolve.Names.key -> body_part;
  read_contract_part : Resolve.Names.key -> contract_part;
  read_generated_parts : Path.t -> body_part * contract_part;
}

type 'form sourced = { source : Resolve.Names.key; form : 'form }

val find_code : body_part -> Tree.t option
val find_graph : body_part -> Graph.t option
val read_body_part : lookups -> Path.t -> body_part sourced option
val read_code : lookups -> Path.t -> Tree.t sourced option
val read_graph : lookups -> Path.t -> Graph.t sourced option
val read_initializer : lookups -> Path.t -> Tree.t sourced option
val read_initializer_graph : lookups -> Path.t -> Graph.t sourced option
val read_contract : lookups -> Path.t -> Tree.contract sourced option
val read_defaults : lookups -> Path.t -> Tree.t Tree.defaults sourced option
val read_default_graphs : lookups -> Path.t -> Graph.t Tree.defaults sourced option
val read_type_clauses : lookups -> Path.t -> Tree.type_clauses sourced option
val is_index_call : _ Core.target -> bool
val list_checked_requires : lookups -> Path.t -> Tree.requirement list
