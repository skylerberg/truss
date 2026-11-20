let make_source (key : Resolve.Names.key) =
  { State.key; definition = key.path; name = Resolve.Names.show_key key }

let read_source_at_key (lookups : Lookups.t) key =
  ignore (lookups.mir.read_body_part key);
  make_source key

let find_source (lookups : Lookups.t) (path : Path.t) =
  Option.map
    (fun ((origin : Interface.form_origin), substitution) ->
      let source =
        match origin with
        | Written key | Inherited key -> make_source key
        | Derived type_key -> { key = type_key; definition = path; name = Path.show path }
      in
      (source, substitution, origin))
    (lookups.mir.find_form_origin path)

let make_trait_substitution (lookups : Lookups.t) (trait : Types.trait_reference) (ty : Types.ty) =
  Types.make_trait_substitution
    (Interface.Definition.read_trait_interface lookups.interface trait.trait).trait_generics
    ~self:ty trait

let find_clauses (lookups : Lookups.t) path callee =
  Option.map
    (fun (contract : Mir.contract) ->
      {
        State.callee;
        parameters = contract.parameters;
        panics_unless = contract.panics_unless;
        requires = contract.requires;
        ensures = contract.ensures;
        decreases = contract.decreases;
        costs = contract.costs;
        callbacks = contract.callbacks;
        inherited = false;
        bindings = Types.no_substitution;
      })
    (Option.map
       (fun ({ form; _ } : Mir.contract Mir.sourced) -> form)
       (Mir.read_contract lookups.mir path))

let holds_todo (lookups : Lookups.t) (key : Resolve.Names.key) =
  match Mir.find_code (lookups.mir.read_body_part key) with
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
  let is_same_argument (left : Types.argument) (right : Types.argument) =
    match (left, right) with Type left, Type right -> Types.equal left right | _ -> left = right
  in
  let named_laws =
    match (Interface.Impls.find_head for_type, lookups.interface.find_trait_header trait.trait) with
    | Some type_head, Some header ->
        List.concat_map
          (fun law ->
            lookups.interface.names.list_law_proofs package { trait = trait.trait; law; type_head })
          header.laws
    | _ -> []
  in
  List.filter_map
    (fun (key : Resolve.Names.key) ->
      match Interface.Definition.find_interface lookups.interface key.path with
      | Some (Interface.Environment.Law_proof_interface proven) -> (
          let variables =
            List.map (fun (generic : Types.generic) -> generic.generic) proven.generics
          in
          match
            Interface.Impls.match_type ~variables Types.no_substitution proven.for_type for_type
          with
          | Some renaming
            when List.equal is_same_argument
                   (List.map (Types.substitute_argument renaming) proven.trait.trait_arguments)
                   trait.trait_arguments ->
              Some (proven.law, (read_source_at_key lookups key, renaming))
          | _ -> None)
      | _ -> Compiler_bug.raise_bug ~stage:"Prover" "%s is not a law proof" (Path.show key.path))
    named_laws

let is_impl_unfinished (lookups : Lookups.t) (key : Resolve.Names.key) =
  List.exists (holds_todo lookups) (lookups.interface.names.list_contained key)

let is_law_unshown (lookups : Lookups.t) (impl : Path.t) (trait : Types.trait_reference) for_type
    name =
  match lookups.interface.names.find_key impl with
  | Some key ->
      is_impl_unfinished lookups key
      || List.exists
           (fun (law, ((proof : State.source), _)) -> law = name && holds_todo lookups proof.key)
           (list_law_proofs lookups (Path.locate_package impl) trait for_type)
  | None -> false

let make_contract ?trait_clauses (lookups : Lookups.t) path callee_clauses =
  let signature = Interface.Impls.read_signature lookups.interface path in
  let is_logic_function =
    match signature with
    | Some (signature : Types.signature) -> (
        (not
           (Types.exists_capability
              (function
                | Types.Capability_parameter _ -> false
                | Types.Built_in _ | Types.Capability _ | Types.Capability_projection _
                | Types.Capability_variable _ | Types.Capability_error _ ->
                    true
                | Types.Capability_unless _ | Types.Capability_unless_values _ ->
                    Compiler_bug.raise_bug ~stage:"Prover" "a capability's base has a condition")
              (Facts.remove_panic_condition signature.uses)))
        && List.for_all
             (fun (info : Types.parameter_info) -> info.mode <> Language.Mode.Mut)
             signature.parameters
        && match signature.receiver with Some (Mut, _) -> false | _ -> true)
    | None -> false
  in
  let result_kind = match signature with Some { output = Lends _; _ } -> `Lends | _ -> `Returns in
  { State.callee_clauses; trait_clauses; restated_clauses = []; is_logic_function; result_kind }

let list_declared_clauses (contract : State.contract) =
  (contract.callee_clauses :: Option.to_list contract.trait_clauses) @ contract.restated_clauses

let select_precondition_clauses (contract : State.contract) =
  match contract.trait_clauses with
  | Some trait_clauses when contract.callee_clauses.requires = [] -> trait_clauses
  | Some _ | None -> contract.callee_clauses

let find_function_contract lookups (path : Path.t) =
  Option.bind (find_source lookups path) (fun (callee, _, _) ->
      Option.map (make_contract lookups path) (find_clauses lookups path callee))

let find_declared_clauses lookups path =
  Option.bind (find_source lookups path) (fun (callee, _, _) -> find_clauses lookups path callee)

let find_trait_clauses lookups (trait : Path.t) name receiver =
  Option.map
    (fun (clauses : State.clauses) -> { clauses with inherited = true })
    (find_declared_clauses lookups (Path.Method { owner = trait; name; receiver }))

let restates ~(trait : Path.t) ~name ~receiver (interface : Types.trait_interface) =
  List.exists
    (fun (restated : Types.restated_method) ->
      restated.restated_name = name
      && restated.restated_receiver = receiver
      && Path.equal restated.declared_by trait)
    interface.restated

let list_implemented_traits (lookups : Lookups.t) ~list_bounds (self_type : Types.ty) ~packages =
  match self_type with
  | Types.Named { path; _ } ->
      List.concat_map
        (fun package ->
          List.filter_map
            (fun (_, impl) ->
              let interface = Interface.Definition.read_impl_interface lookups.interface impl in
              let variables =
                List.map (fun (generic : Types.generic) -> generic.generic) interface.impl_generics
              in
              Option.bind
                (Interface.Impls.match_type ~variables Types.no_substitution interface.for_type
                   self_type) (fun arguments ->
                  let implemented = Types.substitute_trait arguments interface.implements in
                  Option.map
                    (fun _ -> implemented)
                    (Interface.Impls.find_evidence lookups.interface ~list_bounds self_type
                       implemented)))
            (Interface.Impls.list_impls_for_type lookups.interface path package))
        packages
  | _ -> Interface.Properties.list_known_bounds lookups.interface ~list_bounds self_type

let list_restated_clauses (lookups : Lookups.t) ~list_bounds ~packages ~self_type (trait : Path.t)
    name receiver =
  List.filter_map
    (fun (subtrait : Types.trait_reference) ->
      match Interface.Definition.find_trait_interface lookups.interface subtrait.trait with
      | Some interface when restates ~trait ~name ~receiver interface ->
          Option.map
            (fun clauses -> (subtrait, clauses))
            (find_declared_clauses lookups (Path.Method { owner = subtrait.trait; name; receiver }))
      | _ -> None)
    (List.sort_uniq compare (list_implemented_traits lookups ~list_bounds self_type ~packages))

let find_capability_contract lookups (capability : Path.t) name =
  let path = Path.make_capability_method capability name in
  Option.bind (find_source lookups path) (fun (callee, _, _) ->
      Option.map
        (fun callee_clauses ->
          { (make_contract lookups path callee_clauses) with is_logic_function = false })
        (find_clauses lookups path callee))

let find_capability_clauses lookups (capability : Path.t) name =
  find_declared_clauses lookups (Path.make_capability_method capability name)

let find_method_contract lookups (trait : Types.trait_reference) name receiver
    (evidence : Core.evidence) =
  let trait_clauses = find_trait_clauses lookups trait.trait name receiver in
  match evidence with
  | Impl { impl; _ } -> (
      let path = Path.Method { owner = impl; name; receiver } in
      match find_source lookups path with
      | Some (callee, _, (Written _ | Derived _)) ->
          Option.map (make_contract ?trait_clauses lookups path) (find_clauses lookups path callee)
      | Some (_, _, Inherited _) | None -> Option.map (make_contract lookups path) trait_clauses)
  | Bound | Dynamic ->
      Option.map
        (make_contract lookups (Path.Method { owner = trait.trait; name; receiver }))
        trait_clauses

let find_integer_literal (formula : Mir.formula) =
  match formula.value with
  | { statements = []; value = Some (Immediate { value = Integer number; _ }) } -> Some number
  | _ -> None

let deduplicate_counters counters =
  List.fold_left
    (fun distinct counter -> if List.mem counter distinct then distinct else distinct @ [ counter ])
    [] counters

let find_resource (cost : Mir.cost) ~locals : Costs.resource option =
  match cost.resource with
  | Metric metric -> Some (Metric metric)
  | Calls (Function_parameter local) ->
      Option.map
        (fun term -> Costs.Calls (Through term))
        (Locals.find_opt (Core_local local) locals)
  | Calls (Capability path) -> Some (Calls (Capability path))
  | Calls (Capability_method (path, name)) -> Some (Calls (Capability_method (path, name)))
