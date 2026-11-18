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

let find_code = function Body code -> Some code.tree | Initializer _ | No_code -> None
let find_graph = function Body code -> Some code.graph | Initializer _ | No_code -> None

let read_body_part lookups path =
  Option.map
    (fun ((origin : Infer.form_origin), _) ->
      match origin with
      | Written key | Inherited key -> { source = key; form = lookups.read_body_part key }
      | Derived type_key -> { source = type_key; form = fst (lookups.read_generated_parts path) })
    (lookups.find_form_origin path)

let read_contract_part lookups path =
  Option.map
    (fun ((origin : Infer.form_origin), _) ->
      match origin with
      | Written key | Inherited key -> { source = key; form = lookups.read_contract_part key }
      | Derived type_key -> { source = type_key; form = snd (lookups.read_generated_parts path) })
    (lookups.find_form_origin path)

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

let is_index_call (callee : _ Core.target) =
  match callee with
  | Trait_method { trait; name; evidence = Impl _; _ } -> (
      match name with
      | "at" -> Well_known.is Index trait.trait || Well_known.is Index_mut trait.trait
      | "assign" -> Well_known.is Index_assign trait.trait
      | _ -> false)
  | _ -> false

let find_trait_declaration (path : Path.t) =
  match path with
  | Method { owner = Impl { trait; _ }; name; receiver } ->
      Some (Path.Method { owner = trait.path; name; receiver })
  | Top _ | Method _ | Member_constant _ | Impl _ | Derived _ | Test _ | Law_proof _ | Unresolved _
    ->
      None

let find_checked_requires lookups path =
  let select_executable (contract : Tree.contract sourced) =
    match contract.form.requires with
    | _ :: _ as requires
      when List.for_all (fun (requirement : Tree.requirement) -> requirement.is_executable) requires
      ->
        Some { contract with form = requires }
    | _ -> None
  in
  match lookups.find_form_origin path with
  | Some (Written _, _) -> (
      match read_contract lookups path with
      | Some { form = { requires = []; _ }; _ } ->
          Option.bind
            (Option.bind (find_trait_declaration path) (read_contract lookups))
            select_executable
      | Some contract -> select_executable contract
      | None -> None)
  | Some (Inherited _, _) -> Option.bind (read_contract lookups path) select_executable
  | Some (Derived _, _) | None -> None
