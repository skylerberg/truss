type mode = { context : Interface.Elaborator.t; checks_specification : bool }

type t = {
  mutable next : int;
  type_solutions : (int, Types.ty) Hashtbl.t;
  value_solutions : (int, Types.value) Hashtbl.t;
  mutable capability_variable_count : int;
  mutable deferred_capability_equalities : (Types.capability_set * Types.capability_set) list;
  domains : (int, Language.Builtin_type.t list) Hashtbl.t;
  list_rigid_members : Interface.Elaborator.t -> Types.ty -> Language.Builtin_type.t list;
  mutable mode : mode;
  specification_unknowns : (int, unit) Hashtbl.t;
  mutable refused_code_unknown : int option;
  mutable decided_numbers : int list;
}

let create ~context ~list_rigid_members =
  {
    next = 0;
    type_solutions = Hashtbl.create 16;
    value_solutions = Hashtbl.create 4;
    capability_variable_count = 0;
    deferred_capability_equalities = [];
    domains = Hashtbl.create 8;
    list_rigid_members;
    mode = { context; checks_specification = false };
    specification_unknowns = Hashtbl.create 8;
    refused_code_unknown = None;
    decided_numbers = [];
  }

let allocate_unknown unifier =
  unifier.next <- unifier.next + 1;
  if unifier.mode.checks_specification then
    Hashtbl.replace unifier.specification_unknowns unifier.next ();
  unifier.next

let make_fresh_type unifier = Types.Variable (allocate_unknown unifier)

let make_fresh_number unifier domain =
  let number = make_fresh_type unifier in
  Hashtbl.replace unifier.domains unifier.next domain;
  number

let make_fresh_value unifier = Types.Value_variable (allocate_unknown unifier)

let make_fresh_argument unifier (generic : Types.generic) =
  match generic.kind with
  | Value_generic -> Types.Value (make_fresh_value unifier)
  | Type_generic _ -> Types.Type (make_fresh_type unifier)

let make_fresh_capability_variable unifier =
  unifier.capability_variable_count <- unifier.capability_variable_count + 1;
  Types.make_capability_set [ Types.Capability_variable unifier.capability_variable_count ]

let unify_capabilities unifier (left : Types.capability_set) right =
  left = right
  || (Types.has_unsolved_capabilities left || Types.has_unsolved_capabilities right)
     && begin
       unifier.deferred_capability_equalities <-
         (left, right) :: unifier.deferred_capability_equalities;
       true
     end

let rec resolve unifier (type_ : Types.ty) =
  match type_ with
  | Variable index -> (
      match Hashtbl.find_opt unifier.type_solutions index with
      | Some bound -> resolve unifier bound
      | None -> type_)
  | _ -> type_

let rec read_root unifier index =
  match
    (Hashtbl.find_opt unifier.type_solutions index, Hashtbl.find_opt unifier.value_solutions index)
  with
  | Some (Types.Variable next), _ | _, Some (Types.Value_variable next) -> read_root unifier next
  | _ -> index

let rec resolve_value unifier (value : Types.value) =
  match value with
  | Value_variable index -> (
      match Hashtbl.find_opt unifier.value_solutions index with
      | Some bound -> resolve_value unifier bound
      | None -> value)
  | _ -> value

let rec zonk unifier (type_ : Types.ty) : Types.ty =
  let zonk = zonk unifier in
  match resolve unifier type_ with
  | Named { path; arguments } ->
      Named { path; arguments = List.map (zonk_argument unifier) arguments }
  | Projection { base; trait; name } ->
      Projection { base = zonk base; trait = zonk_trait unifier trait; name }
  | Function function_type -> Function (zonk_function unifier function_type)
  | Any trait -> Any (zonk_trait unifier trait)
  | type_ -> type_

and zonk_argument unifier = function
  | Types.Type type_ -> Types.Type (zonk unifier type_)
  | Types.Value value -> Types.Value (resolve_value unifier value)

and zonk_capabilities unifier capabilities =
  Types.replace_capabilities
    (function
      | Types.Capability_projection { base; trait; name } ->
          Some
            (Types.make_capability_set
               [
                 Types.Capability_projection
                   { base = zonk unifier base; trait = zonk_trait unifier trait; name };
               ])
      | _ -> None)
    (Types.map_conditions
       (Types.map_condition_types (zonk unifier) (zonk_trait unifier))
       capabilities)

and zonk_trait unifier (trait : Types.trait_reference) =
  {
    trait with
    trait_arguments = List.map (zonk_argument unifier) trait.trait_arguments;
    associated = List.map (fun (name, type_) -> (name, zonk unifier type_)) trait.associated;
  }

and zonk_function unifier (function_type : Types.function_type) =
  {
    function_type with
    inputs = List.map (fun (mode, type_) -> (mode, zonk unifier type_)) function_type.inputs;
    output = zonk unifier function_type.output;
    uses = zonk_capabilities unifier function_type.uses;
  }

let occurs unifier index =
  Types.exists ~resolve:(resolve unifier) (function Variable other -> other = index | _ -> false)

let find_domain unifier index = Hashtbl.find_opt unifier.domains index

let list_possible_members unifier type_ =
  match resolve unifier type_ with
  | Types.Variable index -> Option.value ~default:[] (find_domain unifier index)
  | (Parameter _ | Projection _) as rigid -> unifier.list_rigid_members unifier.mode.context rigid
  | type_ -> Types.list_scalar_members type_

let is_within unifier type_ set =
  match list_possible_members unifier type_ with
  | [] -> false
  | members -> List.for_all (fun member -> List.mem member set) members

let may_decide unifier index =
  (not unifier.mode.checks_specification) || Hashtbl.mem unifier.specification_unknowns index

let refuses_to_decide unifier index =
  (not (may_decide unifier index))
  && begin
    unifier.refused_code_unknown <- Some index;
    true
  end

let bind unifier index type_ =
  if occurs unifier index type_ || refuses_to_decide unifier index then false
  else begin
    Hashtbl.replace unifier.type_solutions index type_;
    if Hashtbl.mem unifier.domains index then
      unifier.decided_numbers <- index :: unifier.decided_numbers;
    true
  end

let count_solutions unifier = Hashtbl.length unifier.type_solutions

let poison unifier index report =
  Hashtbl.replace unifier.type_solutions (read_root unifier index) (Types.Error report)

let join unifier left right =
  let older = min left right and younger = max left right in
  let domain =
    match (find_domain unifier older, find_domain unifier younger) with
    | Some older_domain, Some younger_domain ->
        Some (List.filter (fun member -> List.mem member younger_domain) older_domain)
    | domain, None | None, domain -> domain
  in
  domain <> Some []
  && (domain = find_domain unifier older || not (refuses_to_decide unifier older))
  && bind unifier younger (Types.Variable older)
  && begin
    Option.iter (Hashtbl.replace unifier.domains older) domain;
    true
  end

type unknown = Unknown_type of int | Unknown_value of int

let list_unknowns unifier (type_ : Types.ty) =
  let unknowns = ref [] in
  let rec collect (type_ : Types.ty) =
    match resolve unifier type_ with
    | Variable index -> unknowns := Unknown_type index :: !unknowns
    | Named { arguments; _ } -> List.iter collect_argument arguments
    | Projection { base; trait = reference; _ } ->
        collect base;
        collect_trait reference
    | Function { inputs; output; _ } ->
        List.iter (fun (_, type_) -> collect type_) inputs;
        collect output
    | Any reference -> collect_trait reference
    | Parameter _ | Never | Integer | Hole | Error _ -> ()
  and collect_argument = function
    | Types.Type type_ -> collect type_
    | Types.Value value -> (
        match resolve_value unifier value with
        | Value_variable index -> unknowns := Unknown_value index :: !unknowns
        | _ -> ())
  and collect_trait (reference : Types.trait_reference) =
    List.iter collect_argument reference.trait_arguments;
    List.iter (fun (_, type_) -> collect type_) reference.associated
  in
  collect type_;
  List.sort_uniq compare !unknowns

let list_argument_unknowns unifier = function
  | Types.Type type_ -> list_unknowns unifier type_
  | Types.Value value -> (
      match resolve_value unifier value with
      | Value_variable index -> [ Unknown_value index ]
      | _ -> [])

let rec unify unifier (left : Types.ty) (right : Types.ty) =
  unifier.refused_code_unknown <- None;
  let left = resolve unifier left and right = resolve unifier right in
  match (left, right) with
  | Types.Variable index, ((Types.Error _ | Types.Hole) as unknown)
  | ((Types.Error _ | Types.Hole) as unknown), Types.Variable index ->
      Hashtbl.replace unifier.type_solutions index unknown;
      true
  | ((Types.Error _ | Types.Hole) as unknown), other
  | other, ((Types.Error _ | Types.Hole) as unknown) ->
      List.iter
        (function
          | Unknown_type index -> Hashtbl.replace unifier.type_solutions index unknown
          | Unknown_value _ -> ())
        (list_unknowns unifier other);
      true
  | Variable left_index, Variable right_index ->
      left_index = right_index || join unifier left_index right_index
  | Variable index, other | other, Variable index ->
      Option.fold ~none:true ~some:(is_within unifier other) (find_domain unifier index)
      && bind unifier index other
  | Named left, Named right ->
      Path.equal left.path right.path && unify_arguments unifier left.arguments right.arguments
  | Parameter left, Parameter right -> left = right
  | Function left, Function right ->
      List.sort_uniq compare left.costs = List.sort_uniq compare right.costs
      && List.length left.inputs = List.length right.inputs
      && List.for_all2
           (fun (left_mode, left) (right_mode, right) ->
             left_mode = right_mode && unify unifier left right)
           left.inputs right.inputs
      && unify unifier left.output right.output
      && unify_capabilities unifier left.uses right.uses
  | Any left, Any right -> unify_trait unifier left right
  | Projection left, Projection right ->
      left.name = right.name
      && Path.equal left.trait.trait right.trait.trait
      && unify_arguments unifier left.trait.trait_arguments right.trait.trait_arguments
      && unify unifier left.base right.base
  | Never, Never | Integer, Integer -> true
  | _ -> false

and unify_arguments unifier left right =
  unifier.refused_code_unknown <- None;
  List.length left = List.length right
  && List.for_all2
       (fun left right ->
         match (left, right) with
         | Types.Type left, Types.Type right -> unify unifier left right
         | Types.Value left, Types.Value right -> unify_value unifier left right
         | Types.Type (Types.Error _), _ | _, Types.Type (Types.Error _) -> true
         | _ -> false)
       left right

and unify_value unifier left right =
  let bind_value index value =
    (not (refuses_to_decide unifier index))
    && begin
      Hashtbl.replace unifier.value_solutions index value;
      true
    end
  in
  match (resolve_value unifier left, resolve_value unifier right) with
  | Value_variable left_index, Value_variable right_index ->
      left_index = right_index
      || bind_value (max left_index right_index) (Value_variable (min left_index right_index))
  | Value_variable index, other | other, Value_variable index -> bind_value index other
  | left, right -> left = right

and unify_trait unifier (left : Types.trait_reference) (right : Types.trait_reference) =
  Path.equal left.trait right.trait
  && unify_arguments unifier left.trait_arguments right.trait_arguments
  && List.length left.associated = List.length right.associated
  && List.for_all2
       (fun (left_name, left) (right_name, right) ->
         left_name = right_name && unify unifier left right)
       left.associated right.associated
