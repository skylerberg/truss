let make_source (key : Resolve.Names.key) = { State.key; definition = key.path }

let read_source_at_key (lookups : Lookups.t) key =
  ignore (lookups.mir.read_body_part key);
  make_source key

let find_source (lookups : Lookups.t) (path : Path.t) =
  Option.map
    (fun ((origin : Interface.form_origin), substitution) ->
      let source =
        match origin with
        | Written key | Inherited key -> make_source key
        | Derived type_key -> { key = type_key; definition = path }
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

let list_todo_origins (lookups : Lookups.t) (key : Resolve.Names.key) =
  match Mir.find_code (lookups.mir.read_body_part key) with
  | Some code ->
      let origins = ref [] in
      Mir.iter_code
        (fun (statement : Mir.statement) ->
          match statement.kind with Jump Todo -> origins := statement.origin :: !origins | _ -> ())
        code;
      List.rev !origins
  | None -> []

let list_law_proofs (lookups : Lookups.t) package (trait : Types.trait_reference)
    (for_type : Types.ty) =
  List.map
    (fun (law, key, renaming) -> (law, (read_source_at_key lookups key, renaming)))
    (Mir.Call_edges.list_law_proofs
       { interface = lookups.interface; mir = lookups.mir }
       package trait for_type)

let list_impl_holes (lookups : Lookups.t) (key : Resolve.Names.key) =
  List.concat_map
    (fun contained ->
      List.map
        (fun origin -> (contained, Obligation.Node origin))
        (list_todo_origins lookups contained))
    (lookups.interface.names.list_contained key)

let has_impl_obligations (lookups : Lookups.t) trait =
  (Interface.Definition.read_trait_interface lookups.interface trait).restated <> []
  ||
  match lookups.interface.find_trait_header trait with
  | Some header -> header.laws <> []
  | None -> false

let list_law_holes (lookups : Lookups.t) (impl : Path.t) (trait : Types.trait_reference) for_type
    name =
  match lookups.interface.names.find_key impl with
  | Some key ->
      list_impl_holes lookups key
      @ List.concat_map
          (fun (law, ((proof : State.source), _)) ->
            if law = name then
              List.map
                (fun origin -> (proof.key, Obligation.Node origin))
                (list_todo_origins lookups proof.key)
            else [])
          (list_law_proofs lookups (Path.locate_package impl) trait for_type)
  | None -> []

let find_callee (context : State.context) path : State.known_callee =
  match Tables.Path_table.find_opt context.callees path with
  | Some callee -> callee
  | None ->
      let lookups = context.lookups in
      let callee : State.known_callee =
        {
          known_signature = lazy (Interface.Impls.read_signature lookups.interface path);
          known_clauses =
            lazy
              (Option.map
                 (fun (source, _, origin) -> (origin, find_clauses lookups path source))
                 (find_source lookups path));
        }
      in
      Tables.Path_table.replace context.callees path callee;
      callee

let read_signature context path = Lazy.force (find_callee context path).known_signature

let list_modified_parts context path position =
  Option.bind (read_signature context path) (fun signature ->
      Types.list_modified_parts signature position)

let find_callee_clauses context path =
  Option.bind (Lazy.force (find_callee context path).known_clauses) snd

let make_contract ?trait_clauses context path callee_clauses =
  let signature = read_signature context path in
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

let find_declared_clauses lookups path =
  Option.bind (find_source lookups path) (fun (callee, _, _) -> find_clauses lookups path callee)

let find_function_contract context (path : Path.t) =
  Option.map (make_contract context path) (find_callee_clauses context path)

let find_trait_clauses context (trait : Path.t) name receiver =
  Option.map
    (fun (clauses : State.clauses) -> { clauses with inherited = true })
    (find_callee_clauses context (Path.Method { owner = trait; name; receiver }))

let restates ~(trait : Path.t) ~name ~receiver (interface : Types.trait_interface) =
  List.exists
    (fun (restated : Types.restated_method) ->
      restated.restated_name = name
      && restated.restated_receiver = receiver
      && Path.equal restated.declared_by trait)
    interface.restated

let list_implemented_traits (lookups : Lookups.t) ~list_bounds (self_type : Types.ty) ~packages
    ~is_wanted =
  match self_type with
  | Types.Named { path; _ } ->
      List.concat_map
        (fun package ->
          List.filter_map
            (fun (implemented, impl) ->
              if not (is_wanted implemented) then None
              else
                let interface = Interface.Definition.read_impl_interface lookups.interface impl in
                let variables =
                  List.map
                    (fun (generic : Types.generic) -> generic.generic)
                    interface.impl_generics
                in
                Option.bind
                  (Interface.Impls.match_type ~variables Types.no_substitution interface.for_type
                     self_type) (fun arguments ->
                    let implemented =
                      Types.substitute_trait_erased arguments interface.implements
                    in
                    Option.map
                      (fun _ -> implemented)
                      (Interface.Impls.find_evidence lookups.interface ~list_bounds self_type
                         implemented)))
            (Interface.Impls.list_impls_for_type lookups.interface path package))
        packages
  | _ ->
      List.filter
        (fun (bound : Types.trait_reference) -> is_wanted bound.trait)
        (Interface.Properties.list_known_bounds lookups.interface ~list_bounds self_type)

let list_restated_clauses (context : State.context) ~packages ~self_type (trait : Path.t) name
    receiver =
  let restates_the_method subtrait =
    match Interface.Definition.find_trait_interface context.lookups.interface subtrait with
    | Some interface -> restates ~trait ~name ~receiver interface
    | None -> false
  in
  List.filter_map
    (fun (subtrait : Types.trait_reference) ->
      Option.map
        (fun clauses -> (subtrait, clauses))
        (find_callee_clauses context (Path.Method { owner = subtrait.trait; name; receiver })))
    (List.sort_uniq compare
       (list_implemented_traits context.lookups ~list_bounds:context.bounds self_type ~packages
          ~is_wanted:restates_the_method))

let find_capability_contract context (capability : Path.t) name =
  let path = Path.make_capability_method capability name in
  Option.map
    (fun callee_clauses ->
      { (make_contract context path callee_clauses) with is_logic_function = false })
    (find_callee_clauses context path)

let find_capability_clauses context (capability : Path.t) name =
  find_callee_clauses context (Path.make_capability_method capability name)

let find_method_contract context (trait : Types.trait_reference) name receiver
    (evidence : Types.evidence) =
  let trait_clauses = find_trait_clauses context trait.trait name receiver in
  match evidence with
  | Impl { impl; _ } | Derived_for_view { viewed = impl; _ } -> (
      let path = Path.Method { owner = impl; name; receiver } in
      match Lazy.force (find_callee context path).known_clauses with
      | Some ((Written _ | Derived _), clauses) ->
          Option.map (make_contract ?trait_clauses context path) clauses
      | Some (Inherited _, _) | None -> Option.map (make_contract context path) trait_clauses)
  | Bound ->
      Option.map
        (make_contract context (Path.Method { owner = trait.trait; name; receiver }))
        trait_clauses

let find_integer_literal (formula : Mir.formula) =
  match formula.value with
  | { statements = []; value = Some (Immediate { value = Integer number; _ }) } -> Some number
  | _ -> None

let mentions_specification (formula : Mir.formula) is_one =
  let mentions = ref false in
  let visit (statement : Mir.statement) =
    match statement.kind with
    | Basic (Assign { value = Specification value; _ }) when is_one value -> mentions := true
    | _ -> ()
  in
  Mir.iter_formula visit formula;
  !mentions

let mentions_result (clause : Mir.formula) =
  mentions_specification clause (function Result -> true | _ -> false)

let mentions_history (clause : Mir.formula) =
  mentions_specification clause (function Yielded -> true | _ -> false)

let find_promiser (lookups : Lookups.t) (source : State.source) : Catalog.Prover.promiser =
  match source.key with
  | { path = Method { owner; _ }; _ }
    when Resolve.Names.find_kind lookups.interface.names owner = Some Resolve.Names.Capability ->
      Capability_promiser
  | _ -> Trait_promiser
