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

let find_code = function Body code -> Some code.tree | Initializer _ | No_code -> None
let find_graph = function Body code -> Some code.graph | Initializer _ | No_code -> None

let read_body_part lookups path =
  Option.map
    (fun ((origin : Infer.form_origin), _) ->
      match origin with
      | Written key | Inherited key -> { source = key; form = lookups.body_part key }
      | Derived type_key -> { source = type_key; form = fst (lookups.generated_parts path) })
    (lookups.form_origin path)

let read_contract_part lookups path =
  Option.map
    (fun ((origin : Infer.form_origin), _) ->
      match origin with
      | Written key | Inherited key -> { source = key; form = lookups.contract_part key }
      | Derived type_key -> { source = type_key; form = snd (lookups.generated_parts path) })
    (lookups.form_origin path)

let select read sourced = Option.map (fun form -> { sourced with form }) (read sourced.form)
let read_from_body_part read lookups path = Option.bind (read_body_part lookups path) (select read)
let read_code = read_from_body_part find_code
let read_graph = read_from_body_part find_graph

let read_initializer =
  read_from_body_part (function Initializer code -> Some code.tree | Body _ | No_code -> None)

let read_initializer_graph =
  read_from_body_part (function Initializer code -> Some code.graph | Body _ | No_code -> None)

let read_from_contract_part read lookups path =
  Option.bind (read_contract_part lookups path) (select read)

let read_contract = read_from_contract_part (fun part -> part.contract)
let read_defaults = read_from_contract_part (fun part -> part.defaults)
let read_default_graphs = read_from_contract_part (fun part -> part.default_graphs)
let read_type_clauses = read_from_contract_part (fun part -> part.type_clauses)
