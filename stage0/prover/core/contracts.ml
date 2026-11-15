open Core
open State

let source_of database (key : Names.key) =
  {
    key = Some key;
    name = Names.show_key key;
    spans = lazy (Option.value (Query.demand database Names.spans key) ~default:[||]);
    text = lazy (Option.value (Query.demand database Names.text key) ~default:"");
  }

let source_at_key database key =
  if Mir.is_lowered database key then Some (source_of database key) else None

let source_at database (path : Path.t) =
  Option.map
    (fun ((origin : Infer.form_origin), substitution) ->
      let source =
        match origin with
        | Written key | Inherited key -> source_of database key
        | Generated -> { key = None; name = Path.show path; spans = lazy [||]; text = lazy "" }
      in
      (source, substitution, origin))
    (Query.demand database Infer.form_origin path)

let trait_substitution database (trait : Types.trait_reference) (ty : Types.ty) =
  let generics =
    match Query.demand database Interface.Environment.interface trait.trait with
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

let part_of ?(inherited = false) database path callee =
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
    (Query.demand database Mir.contract_of_path path)

let holds_todo database (key : Names.key) =
  match Query.demand database Mir.mir key with
  | Some code ->
      let holds = ref false in
      Mir.iter_code
        (fun (statement : Mir.statement) ->
          match statement.kind with Jump Todo -> holds := true | _ -> ())
        code;
      !holds
  | None -> false

let law_proofs database package (trait : Types.trait_reference) (for_type : Types.ty) =
  let same_argument (left : Types.argument) (right : Types.argument) =
    match (left, right) with Type left, Type right -> Types.equal left right | _ -> left = right
  in
  List.concat_map
    (fun module_ ->
      List.filter_map
        (fun (declaration : Names.declaration) ->
          match
            ( declaration.kind,
              Query.demand database Interface.Environment.interface declaration.path )
          with
          | Law_proof, Some (Interface.Environment.Law_proof_interface proven)
            when Path.equal proven.trait.trait trait.trait -> (
              let variables =
                List.map (fun (generic : Types.generic) -> generic.generic) proven.generics
              in
              match Interface.Impls.match_type ~variables [] proven.for_type for_type with
              | Some renaming
                when List.equal same_argument
                       (List.map (Types.substitute_argument renaming) proven.trait.trait_arguments)
                       trait.trait_arguments ->
                  Option.map
                    (fun source -> (proven.law, (source, renaming)))
                    (source_at_key database (Names.key_of declaration))
              | _ -> None)
          | _ -> None)
        (Query.demand database Names.declarations module_))
    (Query.demand database Packages.modules package)

let impl_unfinished database (key : Names.key) =
  List.exists (holds_todo database) (Query.demand database Names.contained key)

let law_unshown database (impl : Path.t) (trait : Types.trait_reference) for_type name =
  match Query.demand database Interface.Summary.key impl with
  | Some key ->
      impl_unfinished database key
      || List.exists
           (fun (law, ((proof : source), _)) ->
             law = name && Option.fold ~none:false ~some:(holds_todo database) proof.key)
           (law_proofs database (Path.package impl) trait for_type)
  | None -> false

let make_contract database path ~own ~others ~definition =
  let signature = Interface.Impls.signature database path in
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
  let definition =
    match definition with
    | Some code when is_logic_function && result_kind = `Returns -> Some (own, code)
    | _ -> None
  in
  { parts = own :: others; is_logic_function; result_kind; definition }

let definition_code ?reading_package database (path : Path.t) =
  match
    Query.demand database
      (match reading_package with
      | Some package when package <> Path.package path -> Mir.exported_definition_of_path
      | _ -> Mir.definition_of_path)
      path
  with
  | Some (Functional definition) -> Some definition
  | Some Not_functional | None -> None

let function_contract ?reading_package database (path : Path.t) =
  Option.bind (source_at database path) (fun (callee, _, _) ->
      Option.map
        (fun own ->
          make_contract database path ~own ~others:[]
            ~definition:(definition_code ?reading_package database path))
        (part_of database path callee))

let trait_part database (trait : Path.t) name receiver =
  let path = Path.Method { owner = trait; name; receiver } in
  Option.bind (source_at database path) (fun (callee, _, _) ->
      part_of ~inherited:true database path callee)

let capability_contract database (capability : Path.t) name =
  let path = Path.Method { owner = capability; name; receiver = Static } in
  Option.bind (source_at database path) (fun (callee, _, _) ->
      Option.map
        (fun own ->
          {
            (make_contract database path ~own ~others:[] ~definition:None) with
            is_logic_function = false;
          })
        (part_of database path callee))

let capability_part database (capability : Path.t) name =
  let path = Path.Method { owner = capability; name; receiver = Static } in
  Option.bind (source_at database path) (fun (callee, _, _) -> part_of database path callee)

let method_contract ?reading_package database (trait : Types.trait_reference) name receiver
    (evidence : evidence) =
  let trait_side = trait_part database trait.trait name receiver in
  match evidence with
  | Impl { impl; _ } -> (
      let path = Path.Method { owner = impl; name; receiver } in
      match source_at database path with
      | Some (callee, _, (Written _ | Generated)) ->
          Option.map
            (fun own ->
              make_contract database path ~own ~others:(Option.to_list trait_side)
                ~definition:(definition_code ?reading_package database path))
            (part_of database path callee)
      | Some (_, _, Inherited _) | None ->
          Option.map
            (fun own ->
              make_contract database path ~own ~others:[]
                ~definition:
                  (definition_code database (Path.Method { owner = trait.trait; name; receiver })))
            trait_side)
  | Bound | Dynamic ->
      Option.map
        (fun own ->
          make_contract database
            (Path.Method { owner = trait.trait; name; receiver })
            ~own ~others:[] ~definition:None)
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

let is_updating_helper database (path : Path.t) =
  match path with
  | Method { receiver = Mut; _ } -> (
      match Interface.Summary.definition database path with
      | Some
          ( _,
            {
              visibility = Private;
              kind = Function { signature = { name = Member_name _; _ }; _ };
              _;
            } ) ->
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
