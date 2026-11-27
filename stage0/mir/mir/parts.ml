type code = { tree : Tree.t; graph : Graph.t }
type body_part = Body of code | Initializer of code | No_code

type contract_part = {
  contract : Tree.contract option;
  defaults : code Tree.default list;
  laws : Tree.law list;
  type_clauses : Tree.type_clauses option;
}

type lookups = {
  find_form_origin : Path.t -> (Interface.form_origin * Types.substitution) option;
  read_body_part : Resolve.Names.key -> body_part;
  read_contract_part : Resolve.Names.key -> contract_part;
  read_generated_parts : Path.t -> body_part * contract_part;
}

type 'form sourced = { source : Resolve.Names.key; form : 'form }

let find_code = function Body code -> Some code.tree | Initializer _ | No_code -> None
let find_graph = function Body code -> Some code.graph | Initializer _ | No_code -> None

let read_body_part lookups path =
  Option.map
    (fun ((origin : Interface.form_origin), _) ->
      match origin with
      | Written key | Inherited key -> { source = key; form = lookups.read_body_part key }
      | Derived type_key -> { source = type_key; form = fst (lookups.read_generated_parts path) })
    (lookups.find_form_origin path)

let read_contract_part lookups path =
  Option.map
    (fun ((origin : Interface.form_origin), _) ->
      match origin with
      | Written key | Inherited key -> { source = key; form = lookups.read_contract_part key }
      | Derived type_key -> { source = type_key; form = snd (lookups.read_generated_parts path) })
    (lookups.find_form_origin path)

let select read sourced = Option.map (fun form -> { sourced with form }) (read sourced.form)
let read_from_body_part read lookups path = Option.bind (read_body_part lookups path) (select read)
let read_code = read_from_body_part find_code
let read_graph = read_from_body_part find_graph
let find_initializer = function Initializer code -> Some code | Body _ | No_code -> None

let read_initializer_code lookups (path : Path.t) =
  match path with
  | Default { owner; variant; name } ->
      Option.bind (read_contract_part lookups owner) (fun sourced ->
          Option.map
            (fun (default : code Tree.default) -> { sourced with form = default.value })
            (List.find_opt
               (fun (default : code Tree.default) ->
                 default.variant = variant && default.name = name)
               sourced.form.defaults))
  | _ -> read_from_body_part find_initializer lookups path

let read_initializer lookups path =
  Option.map
    (fun sourced -> { sourced with form = sourced.form.tree })
    (read_initializer_code lookups path)

let read_initializer_graph lookups path =
  Option.map
    (fun sourced -> { sourced with form = sourced.form.graph })
    (read_initializer_code lookups path)

let read_from_contract_part read lookups path =
  Option.bind (read_contract_part lookups path) (select read)

let read_contract = read_from_contract_part (fun part -> part.contract)
let read_type_clauses = read_from_contract_part (fun part -> part.type_clauses)
let read_defaults = read_from_contract_part (fun part -> Some part.defaults)
