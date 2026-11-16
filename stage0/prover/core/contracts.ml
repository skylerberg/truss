open Core
open State

let source_of (key : Names.key) =
  { key = Some key; name = Names.show_key key; spans = lazy [||]; text = lazy "" }

let source_at_key (lookups : Lookups.t) key =
  ignore (lookups.mir.body_part key);
  source_of key

let home_source (lookups : Lookups.t) key =
  {
    (source_at_key lookups key) with
    spans = lazy (lookups.interface.names.spans key);
    text = lazy (lookups.interface.names.text key);
  }

let source_at (lookups : Lookups.t) (path : Path.t) =
  Option.map
    (fun ((origin : Infer.form_origin), substitution) ->
      let source =
        match origin with
        | Written key | Inherited key -> source_of key
        | Generated -> { key = None; name = Path.show path; spans = lazy [||]; text = lazy "" }
      in
      (source, substitution, origin))
    (lookups.mir.form_origin path)

let trait_substitution (lookups : Lookups.t) (trait : Types.trait_reference) (ty : Types.ty) =
  let generics =
    match Interface.Definition.read_interface lookups.interface trait.trait with
    | Some (Interface.Environment.Trait_interface interface) ->
        List.map (fun (generic : Types.generic) -> generic.generic) interface.trait_generics
    | _ -> []
  in
  let rec pair generics arguments =
    match (generics, arguments) with
    | generic :: generics, argument :: arguments -> (generic, argument) :: pair generics arguments
    | _ -> []
  in
  ({ Types.owner = trait.trait; name = "Self" }, Types.Type ty)
  :: pair generics trait.trait_arguments

let part_of ?(inherited = false) (lookups : Lookups.t) path callee =
  Option.map
    (fun (contract : Mir.contract) ->
      {
        callee;
        parameters = contract.parameters;
        requires = contract.requires;
        ensures = contract.ensures;
        decreases = contract.decreases;
        costs =
          List.filter
            (fun (cost : Mir.cost) ->
              match cost with { resource = Time; bound = Finite; _ } -> false | _ -> true)
            contract.costs;
        callbacks = contract.callbacks;
        inherited;
      })
    (Mir.contract_of_path lookups.mir path)

let holds_todo (lookups : Lookups.t) (key : Names.key) =
  match Mir.code (lookups.mir.body_part key) with
  | Some code ->
      let holds = ref false in
      Mir.iter_code
        (fun (statement : Mir.statement) ->
          match statement.kind with Jump Todo -> holds := true | _ -> ())
        code;
      !holds
  | None -> false

let law_proofs (lookups : Lookups.t) package (trait : Types.trait_reference) (for_type : Types.ty) =
  let same_argument (left : Types.argument) (right : Types.argument) =
    match (left, right) with Type left, Type right -> Types.equal left right | _ -> left = right
  in
  let named_laws =
    match (Interface.Impls.find_head for_type, lookups.interface.trait_header trait.trait) with
    | Some type_head, Some header ->
        List.concat_map
          (fun law ->
            lookups.interface.names.law_proofs package { trait = trait.trait; law; type_head })
          header.laws
    | _ -> []
  in
  List.filter_map
    (fun (key : Names.key) ->
      match Interface.Definition.read_interface lookups.interface key.path with
      | Some (Interface.Environment.Law_proof_interface proven) -> (
          let variables =
            List.map (fun (generic : Types.generic) -> generic.generic) proven.generics
          in
          match Interface.Impls.match_type ~variables [] proven.for_type for_type with
          | Some renaming
            when List.equal same_argument
                   (List.map (Types.substitute_argument renaming) proven.trait.trait_arguments)
                   trait.trait_arguments ->
              Some (proven.law, (source_at_key lookups key, renaming))
          | _ -> None)
      | _ -> None)
    named_laws

let impl_unfinished (lookups : Lookups.t) (key : Names.key) =
  List.exists (holds_todo lookups) (lookups.interface.names.contained key)

let law_unshown (lookups : Lookups.t) (impl : Path.t) (trait : Types.trait_reference) for_type name
    =
  match lookups.interface.names.key impl with
  | Some key ->
      impl_unfinished lookups key
      || List.exists
           (fun (law, ((proof : source), _)) ->
             law = name && Option.fold ~none:false ~some:(holds_todo lookups) proof.key)
           (law_proofs lookups (Path.package impl) trait for_type)
  | None -> false

let make_contract (lookups : Lookups.t) path ~own ~others =
  let signature = Interface.Impls.read_signature lookups.interface path in
  let is_logic_function =
    match signature with
    | Some (signature : Types.signature) -> (
        signature.uses = Types.no_capabilities
        && signature.terminates
        && List.for_all
             (fun (info : Types.parameter_info) -> info.mode <> Types.Mut)
             signature.parameters
        && match signature.receiver with Some (Mut, _) -> false | _ -> true)
    | None -> false
  in
  let result_kind = match signature with Some { output = Lends _; _ } -> `Lends | _ -> `Returns in
  { parts = own :: others; is_logic_function; result_kind }

let function_contract lookups (path : Path.t) =
  Option.bind (source_at lookups path) (fun (callee, _, _) ->
      Option.map
        (fun own -> make_contract lookups path ~own ~others:[])
        (part_of lookups path callee))

let trait_part lookups (trait : Path.t) name receiver =
  let path = Path.Method { owner = trait; name; receiver } in
  Option.bind (source_at lookups path) (fun (callee, _, _) ->
      part_of ~inherited:true lookups path callee)

let capability_contract lookups (capability : Path.t) name =
  let path = Path.Method { owner = capability; name; receiver = Static } in
  Option.bind (source_at lookups path) (fun (callee, _, _) ->
      Option.map
        (fun own -> { (make_contract lookups path ~own ~others:[]) with is_logic_function = false })
        (part_of lookups path callee))

let capability_part lookups (capability : Path.t) name =
  let path = Path.Method { owner = capability; name; receiver = Static } in
  Option.bind (source_at lookups path) (fun (callee, _, _) -> part_of lookups path callee)

let method_contract lookups (trait : Types.trait_reference) name receiver (evidence : evidence) =
  let trait_side = trait_part lookups trait.trait name receiver in
  match evidence with
  | Impl { impl; _ } -> (
      let path = Path.Method { owner = impl; name; receiver } in
      match source_at lookups path with
      | Some (callee, _, (Written _ | Generated)) ->
          Option.map
            (fun own -> make_contract lookups path ~own ~others:(Option.to_list trait_side))
            (part_of lookups path callee)
      | Some (_, _, Inherited _) | None ->
          Option.map (fun own -> make_contract lookups path ~own ~others:[]) trait_side)
  | Bound | Dynamic ->
      Option.map
        (fun own ->
          make_contract lookups
            (Path.Method { owner = trait.trait; name; receiver })
            ~own ~others:[])
        trait_side

let literal (formula : Mir.formula) =
  match formula.value with
  | { statements = []; value = Some (Constant { value = Integer number; _ }) } -> Some number
  | _ -> None

let distinct_counters counters =
  List.fold_left
    (fun distinct counter -> if List.mem counter distinct then distinct else distinct @ [ counter ])
    [] counters

let resource_of (cost : Mir.cost) ~locals : Costs.resource option =
  match cost.resource with
  | Time -> Some Time
  | Allocations -> Some Allocations
  | Allocated_bytes -> Some Allocated_bytes
  | Calls (Function_parameter local) ->
      Option.map (fun term -> Costs.Calls (Through term)) (Locals.find_opt local locals)
  | Calls (Capability path) -> Some (Calls (Capability path))
  | Calls (Capability_method (path, name)) -> Some (Calls (Capability_method (path, name)))

let is_updating_helper (lookups : Lookups.t) (path : Path.t) =
  match path with
  | Method { receiver = Mut; _ } -> (
      match Option.map lookups.interface.names.definition (lookups.interface.names.key path) with
      | Some
          {
            visibility = Private;
            kind = Function { signature = { name = Member_name _; _ }; _ };
            _;
          } ->
          true
      | _ -> false)
  | _ -> false

let comparison (comparison : comparison) =
  match comparison with
  | Equal -> Some "="
  | Less -> Some "<"
  | Less_equal -> Some "<="
  | Greater -> Some ">"
  | Greater_equal -> Some ">="
  | Not_equal -> None
