let make_source (key : Resolve.Names.key) =
  { State.key = Some key; name = Resolve.Names.show_key key }

let read_source_at_key (lookups : Lookups.t) key =
  ignore (lookups.mir.body_part key);
  make_source key

let find_source (lookups : Lookups.t) (path : Path.t) =
  Option.map
    (fun ((origin : Infer.form_origin), substitution) ->
      let source =
        match origin with
        | Written key | Inherited key -> make_source key
        | Derived _ -> { key = None; name = Path.show path }
      in
      (source, substitution, origin))
    (lookups.mir.form_origin path)

let make_trait_substitution (lookups : Lookups.t) (trait : Types.trait_reference) (ty : Types.ty) =
  match Interface.Definition.read_trait_interface lookups.interface trait.trait with
  | Some interface -> Interface.Properties.make_trait_substitution interface ~self:ty trait
  | None -> [ (Types.make_self_parameter trait.trait, Types.Type ty) ]

let find_part ?(inherited = false) (lookups : Lookups.t) path callee =
  Option.map
    (fun (contract : Mir.contract) ->
      {
        State.callee;
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
    (Option.map
       (fun ({ form; _ } : Mir.contract Mir.sourced) -> form)
       (Mir.read_contract lookups.mir path))

let holds_todo (lookups : Lookups.t) (key : Resolve.Names.key) =
  match Mir.find_code (lookups.mir.body_part key) with
  | Some code ->
      let holds = ref false in
      Mir.iter_code
        (fun (statement : Mir.statement) ->
          match statement.kind with Jump Todo -> holds := true | _ -> ())
        code;
      !holds
  | None -> false

let list_law_proofs (lookups : Lookups.t) package (trait : Types.trait_reference)
    (for_type : Types.ty) =
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
    (fun (key : Resolve.Names.key) ->
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
              Some (proven.law, (read_source_at_key lookups key, renaming))
          | _ -> None)
      | _ -> None)
    named_laws

let is_impl_unfinished (lookups : Lookups.t) (key : Resolve.Names.key) =
  List.exists (holds_todo lookups) (lookups.interface.names.contained key)

let law_unshown (lookups : Lookups.t) (impl : Path.t) (trait : Types.trait_reference) for_type name
    =
  match lookups.interface.names.key impl with
  | Some key ->
      is_impl_unfinished lookups key
      || List.exists
           (fun (law, ((proof : State.source), _)) ->
             law = name && Option.fold ~none:false ~some:(holds_todo lookups) proof.key)
           (list_law_proofs lookups (Path.locate_package impl) trait for_type)
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
  { State.parts = own :: others; is_logic_function; result_kind }

let find_function_contract lookups (path : Path.t) =
  Option.bind (find_source lookups path) (fun (callee, _, _) ->
      Option.map
        (fun own -> make_contract lookups path ~own ~others:[])
        (find_part lookups path callee))

let find_trait_part lookups (trait : Path.t) name receiver =
  let path = Path.Method { owner = trait; name; receiver } in
  Option.bind (find_source lookups path) (fun (callee, _, _) ->
      find_part ~inherited:true lookups path callee)

let find_capability_contract lookups (capability : Path.t) name =
  let path = Path.make_capability_method capability name in
  Option.bind (find_source lookups path) (fun (callee, _, _) ->
      Option.map
        (fun own -> { (make_contract lookups path ~own ~others:[]) with is_logic_function = false })
        (find_part lookups path callee))

let find_capability_part lookups (capability : Path.t) name =
  let path = Path.make_capability_method capability name in
  Option.bind (find_source lookups path) (fun (callee, _, _) -> find_part lookups path callee)

let method_contract lookups (trait : Types.trait_reference) name receiver (evidence : Core.evidence)
    =
  let trait_side = find_trait_part lookups trait.trait name receiver in
  match evidence with
  | Impl { impl; _ } -> (
      let path = Path.Method { owner = impl; name; receiver } in
      match find_source lookups path with
      | Some (callee, _, (Written _ | Derived _)) ->
          Option.map
            (fun own -> make_contract lookups path ~own ~others:(Option.to_list trait_side))
            (find_part lookups path callee)
      | Some (_, _, Inherited _) | None ->
          Option.map (fun own -> make_contract lookups path ~own ~others:[]) trait_side)
  | Bound | Dynamic ->
      Option.map
        (fun own ->
          make_contract lookups
            (Path.Method { owner = trait.trait; name; receiver })
            ~own ~others:[])
        trait_side

let find_integer_literal (formula : Mir.formula) =
  match formula.value with
  | { statements = []; value = Some (Constant { value = Integer number; _ }) } -> Some number
  | _ -> None

let deduplicate_counters counters =
  List.fold_left
    (fun distinct counter -> if List.mem counter distinct then distinct else distinct @ [ counter ])
    [] counters

let find_resource (cost : Mir.cost) ~locals : Costs.resource option =
  match cost.resource with
  | Time -> Some Time
  | Allocations -> Some Allocations
  | Allocated_bytes -> Some Allocated_bytes
  | Calls (Function_parameter local) ->
      Option.map
        (fun term -> Costs.Calls (Through term))
        (Locals.find_opt (Core_local local) locals)
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

let find_comparison_operator (comparison : Core.comparison) =
  match comparison with
  | Equal -> Some "="
  | Less -> Some "<"
  | Less_equal -> Some "<="
  | Greater -> Some ">"
  | Greater_equal -> Some ">="
  | Not_equal -> None
