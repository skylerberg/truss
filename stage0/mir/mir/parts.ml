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

let code = function Body code -> Some code.tree | Initializer _ | No_code -> None
let graph = function Body code -> Some code.graph | Initializer _ | No_code -> None

let body_part_of_path lookups path =
  Option.map
    (fun ((origin : Infer.form_origin), _) ->
      match origin with
      | Written key | Inherited key -> { source = key; form = lookups.body_part key }
      | Derived type_key -> { source = type_key; form = fst (lookups.generated_parts path) })
    (lookups.form_origin path)

let contract_part_of_path lookups path =
  Option.map
    (fun ((origin : Infer.form_origin), _) ->
      match origin with
      | Written key | Inherited key -> { source = key; form = lookups.contract_part key }
      | Derived type_key -> { source = type_key; form = snd (lookups.generated_parts path) })
    (lookups.form_origin path)

let select read sourced = Option.map (fun form -> { sourced with form }) (read sourced.form)
let of_body_part read lookups path = Option.bind (body_part_of_path lookups path) (select read)
let code_of_path = of_body_part code
let graph_of_path = of_body_part graph

let initializer_of_path =
  of_body_part (function Initializer code -> Some code.tree | Body _ | No_code -> None)

let initializer_graph_of_path =
  of_body_part (function Initializer code -> Some code.graph | Body _ | No_code -> None)

let of_contract_part read lookups path =
  Option.bind (contract_part_of_path lookups path) (select read)

let contract_of_path = of_contract_part (fun part -> part.contract)
let defaults_of_path = of_contract_part (fun part -> part.defaults)
let default_graphs_of_path = of_contract_part (fun part -> part.default_graphs)
let type_clauses_of_path = of_contract_part (fun part -> part.type_clauses)
