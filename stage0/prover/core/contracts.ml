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

type known_callee = {
  known_signature : Types.signature option Lazy.t;
  known_clauses : (Interface.form_origin * State.clauses option) option Lazy.t;
}

let callees : known_callee Tables.Path_table.t Private_state.key =
  Private_state.make_key (fun () -> Tables.Path_table.create 16)

let find_callee (environment : State.environment) path =
  let callees = Private_state.read environment.memos callees in
  match Tables.Path_table.find_opt callees path with
  | Some callee -> callee
  | None ->
      let lookups = environment.lookups in
      let callee =
        {
          known_signature = lazy (Interface.Impls.read_signature lookups.interface path);
          known_clauses =
            lazy
              (Option.map
                 (fun (source, _, origin) -> (origin, find_clauses lookups path source))
                 (find_source lookups path));
        }
      in
      Tables.Path_table.replace callees path callee;
      callee

let read_signature (environment : State.environment) path =
  Lazy.force (find_callee environment path).known_signature

let list_modified_parts (environment : State.environment) path position =
  Option.bind (read_signature environment path) (fun signature ->
      Types.list_modified_parts signature position)

let find_callee_clauses (environment : State.environment) path =
  Option.bind (Lazy.force (find_callee environment path).known_clauses) snd

let make_contract ?trait_clauses (environment : State.environment) path callee_clauses =
  let signature = read_signature environment path in
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
              (Facts.remove_panic signature.uses)))
        && List.for_all
             (fun (info : Types.parameter_info) -> info.mode <> Language.Mode.Mut)
             signature.parameters
        && match signature.receiver with Some (Mut, _) -> false | _ -> true)
    | None -> false
  in
  let result_kind = match signature with Some { output = Lends _; _ } -> `Lends | _ -> `Returns in
  { State.callee_clauses; trait_clauses; restated_clauses = []; is_logic_function; result_kind }

let select_precondition_clauses (contract : State.contract) =
  match contract.trait_clauses with
  | Some trait_clauses when contract.callee_clauses.requires = [] -> trait_clauses
  | Some _ | None -> contract.callee_clauses

let list_clause_sets (contract : State.contract) =
  (contract.callee_clauses :: Option.to_list contract.trait_clauses) @ contract.restated_clauses

let find_declared_clauses lookups path =
  Option.bind (find_source lookups path) (fun (callee, _, _) -> find_clauses lookups path callee)

let find_inherited_clauses (environment : State.environment) (path : Path.t) =
  Option.bind (Interface.Impls.find_implemented_method environment.lookups.interface path)
    (fun (implemented : Interface.Impls.implemented_method) ->
      Option.map
        (fun (clauses : State.clauses) ->
          ({ clauses with inherited = true }, implemented.implementation.substitution))
        (find_callee_clauses environment implemented.declaration))

let find_function_contract (environment : State.environment) (path : Path.t) =
  Option.map
    (make_contract
       ?trait_clauses:(Option.map fst (find_inherited_clauses environment path))
       environment path)
    (find_callee_clauses environment path)

let list_added_clauses (environment : State.environment) (path : Path.t) =
  List.filter_map
    (fun ({ restating_method; substitution; holds_when } : Interface.Impls.added_clauses) ->
      Option.map
        (fun (clauses : State.clauses) ->
          ( {
              clauses with
              inherited = true;
              ensures =
                List.map
                  (fun (clause : Mir.formula) ->
                    { clause with holds_when = clause.holds_when @ holds_when })
                  clauses.ensures;
              costs =
                List.map
                  (fun (cost : Mir.cost) -> { cost with holds_when = cost.holds_when @ holds_when })
                  clauses.costs;
            },
            substitution ))
        (find_callee_clauses environment restating_method))
    (Interface.Impls.list_added_clauses environment.lookups.interface path)

let restates (lookups : Lookups.t) ~self_type (subtrait : Types.trait_reference)
    (trait : Types.trait_reference) ~name ~receiver =
  List.exists
    (fun (restated : Types.restated_method) ->
      restated.restated_name = name
      && restated.restated_receiver = receiver
      &&
      match
        Interface.Impls.find_trait_restated_by lookups.interface ~self:self_type subtrait restated
      with
      | Some declared -> Interface.Impls.is_same_trait declared trait
      | None -> false)
    (Interface.Definition.read_trait_interface lookups.interface subtrait.trait).restated

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

let list_restated_clauses (environment : State.environment) ~packages ~self_type
    (trait : Types.trait_reference) name receiver =
  let restates_a_method subtrait =
    match Interface.Definition.find_trait_interface environment.lookups.interface subtrait with
    | Some interface -> interface.restated <> []
    | None -> false
  in
  List.filter_map
    (fun (subtrait : Types.trait_reference) ->
      if restates environment.lookups ~self_type subtrait trait ~name ~receiver then
        Option.map
          (fun clauses -> (subtrait, clauses))
          (find_callee_clauses environment (Path.Method { owner = subtrait.trait; name; receiver }))
      else None)
    (List.sort_uniq compare
       (list_implemented_traits environment.lookups ~list_bounds:environment.bounds self_type
          ~packages ~is_wanted:restates_a_method))

let find_capability_contract (environment : State.environment) (capability : Path.t) name =
  let path = Path.make_capability_method capability name in
  Option.map
    (fun callee_clauses ->
      { (make_contract environment path callee_clauses) with is_logic_function = false })
    (find_callee_clauses environment path)

let find_method_contract (environment : State.environment) (trait : Types.trait_reference) name
    receiver (evidence : Types.evidence) =
  let declaration = Path.Method { owner = trait.trait; name; receiver } in
  let find_declared_contract path =
    Option.map
      (fun (clauses : State.clauses) ->
        make_contract environment path { clauses with inherited = true })
      (find_callee_clauses environment declaration)
  in
  match evidence with
  | Impl { impl; _ } | Derived_for_view { viewed = impl; _ } -> (
      let path = Path.Method { owner = impl; name; receiver } in
      match Lazy.force (find_callee environment path).known_clauses with
      | Some ((Written _ | Derived _), _) -> find_function_contract environment path
      | Some (Inherited _, _) | None -> find_declared_contract path)
  | Bound -> find_declared_contract declaration

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

let mentions_visited (clause : Mir.formula) =
  mentions_specification clause (function Visited -> true | _ -> false)

let mentions_final_result (clause : Mir.formula) =
  mentions_specification clause (function Final_result -> true | _ -> false)

let find_promiser (lookups : Lookups.t) (source : State.source) : Catalog.Prover.promiser =
  match source.key with
  | { path = Method { owner; _ }; _ }
    when Resolve.Names.find_kind lookups.interface.names owner = Some Resolve.Names.Capability ->
      Capability_promiser
  | _ -> Trait_promiser

let make_entry_frame frame (clauses : State.clauses) ~arguments ~substitution =
  let locals, types, self =
    List.fold_left
      (fun (locals, types, self) (position, (parameter : Mir.parameter)) ->
        match (parameter.local, List.assoc_opt position arguments) with
        | Self, Some term -> (locals, types, Some (term, parameter.type_))
        | local, Some term ->
            ( Locals.add (Core_local local) term locals,
              Locals.add (Core_local local) parameter.type_ types,
              self )
        | _, None -> (locals, types, self))
      (Locals.empty, Locals.empty, None)
      (List.mapi (fun position parameter -> (position, parameter)) clauses.parameters)
  in
  let callbacks =
    List.filter_map
      (fun (position, callback) ->
        match (List.nth_opt clauses.parameters position, List.assoc_opt position arguments) with
        | Some (parameter : Mir.parameter), Some term -> (
            match Types.substitute_erased substitution parameter.type_ with
            | Types.Function function_type ->
                Some
                  ( term,
                    ( function_type,
                      State.Own { name = Facts.read_parameter_name parameter; callback } ) )
            | _ -> None)
        | _ -> None)
      clauses.callbacks
  in
  {
    frame with
    State.source = clauses.callee;
    locals;
    types;
    old_locals = locals;
    self = Option.map fst self;
    old_self = Option.map fst self;
    self_type = Option.map (fun (_, ty) -> Types.substitute_erased substitution ty) self;
    result = None;
    visited = None;
    final_result = None;
    makes_obligations = false;
    substitution;
    callbacks;
  }

let make_exit_frame frame (clauses : State.clauses) ~entries ~exits ~result ~substitution =
  let entry = make_entry_frame frame clauses ~arguments:entries ~substitution in
  let exit_ = make_entry_frame frame clauses ~arguments:exits ~substitution in
  { exit_ with old_locals = entry.locals; old_self = entry.self; result }
