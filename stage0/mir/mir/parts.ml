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

let code = function Body code -> Some code.tree | Initializer _ | No_code -> None
let graph = function Body code -> Some code.graph | Initializer _ | No_code -> None

let body_part_of_path lookups path =
  match lookups.form_origin path with
  | Some ((Written key | Inherited key), _) -> lookups.body_part key
  | Some (Generated, _) -> fst (lookups.generated_parts path)
  | None -> No_code

let contract_part_of_path lookups path =
  match lookups.form_origin path with
  | Some ((Written key | Inherited key), _) -> Some (lookups.contract_part key)
  | Some (Generated, _) -> Some (snd (lookups.generated_parts path))
  | None -> None

let code_of_path lookups path = code (body_part_of_path lookups path)
let graph_of_path lookups path = graph (body_part_of_path lookups path)

let initializer_of_path lookups path =
  match body_part_of_path lookups path with
  | Initializer code -> Some code.tree
  | Body _ | No_code -> None

let initializer_graph_of_path lookups path =
  match body_part_of_path lookups path with
  | Initializer code -> Some code.graph
  | Body _ | No_code -> None

let of_contract_part read lookups path = Option.bind (contract_part_of_path lookups path) read
let contract_of_path = of_contract_part (fun part -> part.contract)
let defaults_of_path = of_contract_part (fun part -> part.defaults)
let default_graphs_of_path = of_contract_part (fun part -> part.default_graphs)
let type_clauses_of_path = of_contract_part (fun part -> part.type_clauses)

let is_generated lookups path =
  match lookups.form_origin path with
  | Some (Generated, _) -> true
  | Some ((Written _ | Inherited _), _) | None -> false
