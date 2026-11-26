let make_context ?node ?(condition = []) ?(keeps_termination = true) ?(keeps_failures = true)
    ?panic_condition ?blocked_holders ?proven_laws (lookups : Lookups.t) ~home ~current ~terminates
    ~measures ~inherits_precondition =
  let node = Option.value node ~default:current in
  let rec context =
    {
      State.environment =
        {
          lookups;
          current;
          node;
          home;
          condition;
          bounds = Encoding.list_definition_bounds lookups ~current ~condition;
          disjoint = lookups.list_must_be_disjoint home;
          inherits_precondition;
          ranking = terminates && measures = [] && lookups.list_recursion_group node <> [];
          terminates;
          proven_laws;
          policy = Obligations.make_policy ~keeps_termination ~keeps_failures ~panic_condition;
          visible_types = Tables.Type_table.create 16;
          callees = Tables.Path_table.create 16;
        };
      skipped_conditions = [];
      run_body = (fun frame ~lambdas body -> Reader.read_body context frame ~lambdas body);
      read_formula =
        (fun frame formula ~arguments -> Reader.read_formula context frame formula ~arguments);
      local_names = Tables.Local_table.create 16;
      local_origins = Tables.Local_table.create 16;
      query = Query.create ();
      axioms = Contract_axioms.make_state ();
      termination = Termination.make_state ~measures;
      validity = Validity.make_state ();
      callbacks = Callbacks.make_state ();
      lending = Lending.make_state ();
      cost = Counters.make_state ?blocked_holders ();
      logs = [];
      powers = [];
      lambda_definitions = Tables.Symbol_table.create 8;
      models = Tables.Model_table.create 16;
      holes = [];
      unfinished = [];
      indexes = [];
    }
  in
  context

let make_outcome (context : State.context) =
  {
    Obligation.obligations = Query.list_obligations context.query;
    holes = List.rev context.holes;
    evaluation = None;
  }

let note_entry (frame : State.frame) term ~name =
  match term with
  | Logic.Symbol symbol -> { frame with entry = (symbol, name) :: frame.entry }
  | _ -> frame

let make_empty_frame (environment : State.environment) (query : Query.t) source =
  {
    State.environment;
    query;
    source;
    entry = [];
    locals = Locals.empty;
    types = Locals.empty;
    old_locals = Locals.empty;
    self = None;
    old_self = None;
    result = None;
    condition = Logic.Boolean true;
    makes_obligations = true;
    is_ghost = false;
    bound = [];
    binders = [];
    substitution = Types.no_substitution;
    self_type = None;
    aliases = Locals.empty;
    lends = Locals.empty;
    callbacks = [];
    requires_being_read = None;
    callees_whose_requires_are_read = [];
    provided = [];
    panics = false;
    can_declare_panic = false;
    instantiating = [];
    obligation_condition = [];
    is_reading_callback = false;
    validating = [];
    terminates = environment.terminates;
    visited = None;
    final_result = None;
    spent = [];
  }

let is_capability_implementation (lookups : Lookups.t) (path : Path.t) =
  match path with
  | Method { owner; _ } -> (
      match Interface.Definition.find_impl_interface lookups.interface owner with
      | Some impl ->
          Resolve.Names.find_kind lookups.interface.names impl.implements.trait
          = Some Resolve.Names.Capability
      | None -> false)
  | _ -> false

let read_requires (context : State.context) (frame : State.frame) (requirement : Mir.formula) =
  let after, term =
    Validity.read_specification ~holds_when:requirement.holds_when context
      { frame with requires_being_read = Some requirement.origin }
      requirement
  in
  ({ after with requires_being_read = frame.requires_being_read }, term)

let rec run_blocking ?blocked_holders translate =
  try translate ?blocked_holders ()
  with Counters.Blocks_credited_potential blocked_holders ->
    run_blocking ~blocked_holders translate

let translate_run ~substitution ~condition ~assumes_panic_condition (lookups : Lookups.t)
    (source : State.source) ~path =
  run_blocking @@ fun ?blocked_holders () ->
  let contract =
    match Mir.read_contract lookups.mir path with
    | Some { form; _ } -> form
    | None -> Facts.raise_bug "`%s` has no MIR of its contract" (Resolve.Names.show_key source.key)
  in
  let parameters = contract.parameters in
  let signature =
    Option.map
      (Types.map_signature (Types.substitute_erased substitution))
      (Interface.Impls.read_signature lookups.interface path)
  in
  let is_update_step, is_specification_only =
    match signature with
    | Some (signature : Types.signature) -> (signature.is_update_step, signature.specification_only)
    | None -> (false, false)
  in
  let uses =
    match signature with
    | Some (signature : Types.signature) -> signature.uses
    | None -> Types.make_capability_set [ Built_in Run_forever ]
  in
  let implies = Conditions.implies lookups ~current:path in
  let terminates = is_specification_only || Types.terminates_when ~implies condition uses in
  let keeps_termination =
    condition = [] || Types.find_unless (Built_in Run_forever) uses = Some condition
  in
  let keeps_failures =
    assumes_panic_condition || condition = []
    || Types.find_unless (Built_in Panic) uses = Some condition
  in
  let panics =
    (not assumes_panic_condition) && Conditions.may_panic lookups ~current:path ~condition uses
  in
  let panic_condition =
    if assumes_panic_condition then
      Some
        (List.map
           (fun (requirement : Mir.requirement) -> Facts.quote source requirement.clause.origin)
           contract.panics_unless)
    else None
  in
  let can_declare_panic = not (Types.may_use (Built_in Panic) uses) in
  let home = source.key in
  let measures =
    List.filter
      (fun (measure : Mir.formula) -> implies condition measure.holds_when)
      contract.decreases
  in
  let context =
    make_context lookups ~condition ~keeps_termination ~keeps_failures ?panic_condition
      ?blocked_holders ~home ~current:path
      ~node:
        (Mir.Call_edges.resolve_node
           { interface = lookups.interface; mir = lookups.mir }
           path substitution)
      ~terminates ~measures
      ~inherits_precondition:
        (Option.is_some (Interface.Impls.find_implemented_method lookups.interface path))
  in
  List.iter
    (fun (measure : Mir.formula) ->
      ignore (Conditions.decide context ~substitution:Types.no_substitution measure.holds_when))
    contract.decreases;
  let keep_clauses = Conditions.keep_holding context in
  let inherited =
    Option.map
      (fun (clauses, substitution) -> (keep_clauses ~substitution clauses, substitution))
      (Contracts.find_inherited_clauses context.environment path)
  in
  let own, promises =
    match Contracts.find_function_contract context.environment path with
    | Some resolved ->
        let own =
          keep_clauses ~substitution:Types.no_substitution
            { resolved.callee_clauses with callee = source }
        in
        ( own,
          Contracts.list_promises
            { resolved with callee_clauses = own; trait_clauses = Option.map fst inherited } )
    | None -> Facts.raise_bug "`%s` has no contract" (Resolve.Names.show_key source.key)
  in
  let pair_up terms =
    match (inherited, parameters, terms) with
    | Some ((clauses : State.clauses), _), { local = Self; _ } :: _, _ :: rest
      when not
             (List.exists
                (fun (parameter : Mir.parameter) -> parameter.local = Self)
                clauses.parameters) ->
        rest
    | _ -> terms
  in
  let output = match signature with Some { output = Returns ty; _ } -> Some ty | _ -> None in
  let start =
    List.fold_left
      (fun frame (parameter : Mir.parameter) ->
        match parameter.local with
        | Self ->
            let self_type = Encoding.substitute_type frame parameter.type_ in
            let self = Encoding.arrive frame "self" self_type in
            Validity.assume_valid context frame ~includes_invariants:(not is_update_step) self_type
              self;
            { (note_entry frame self ~name:None) with self = Some self; self_type = Some self_type }
        | local ->
            let ty = Encoding.substitute_type frame parameter.type_ in
            let name = Facts.read_parameter_name parameter in
            let term = Encoding.arrive frame ("parameter." ^ name) ty in
            Validity.assume_valid context frame ty term;
            Facts.bind (note_entry frame term ~name:(Some name)) (Core_local local) ty term)
      {
        (make_empty_frame context.environment context.query source) with
        substitution;
        is_ghost = is_specification_only;
        panics;
        can_declare_panic;
      }
      parameters
  in
  let start = { start with old_locals = start.locals; old_self = start.self } in
  let start =
    Callbacks.bind_own start
      (List.filter_map
         (fun (position, callback) ->
           Option.map
             (fun (parameter : Mir.parameter) ->
               (parameter.local, Facts.read_parameter_name parameter, callback))
             (List.nth_opt parameters position))
         contract.callbacks)
  in
  Termination.enter_definition context start;
  let trait_declaration =
    match (Interface.Impls.find_implemented_method lookups.interface path, path) with
    | Some { declaration; _ }, _ -> Some declaration
    | None, Method { owner; name; receiver }
      when Option.is_some
             (Interface.Definition.find_trait_method lookups.interface owner ~name ~receiver) ->
        Some path
    | None, _ -> None
  in
  (match Option.bind trait_declaration (Interface.Impls.read_signature lookups.interface) with
  | Some declared
    when condition = []
         && lookups.may_abort context.environment.node
         && Types.states_no_allocation declared.costs ->
      Obligations.oblige start Whole_definition (May_not_return_under_no_allocation This_method)
        (Logic.Boolean false)
  | Some _ | None -> ());
  let output = Option.map (Encoding.substitute_type start) output in
  let lends =
    match signature with
    | Some { output = Lends (_, part); _ } ->
        Lending.enter_method context ~part_type:(Encoding.substitute_type start part);
        true
    | Some { output = Returns _; _ } | None -> false
  in
  let list_values (at : State.frame) =
    List.filter_map
      (fun (parameter : Mir.parameter) ->
        match parameter.local with
        | Self -> at.self
        | local -> Locals.find_opt (Core_local local) at.locals)
      parameters
  in
  let list_paired_values (at : State.frame) = pair_up (list_values at) in
  let entry_terms = list_paired_values start in
  let read_in ?result (at : State.frame) (clauses : State.clauses) =
    match inherited with
    | Some (_, substitution) when clauses.inherited ->
        let number terms = List.mapi (fun position term -> (position, term)) terms in
        let inside =
          {
            (Contracts.make_exit_frame at clauses ~entries:(number entry_terms)
               ~exits:(number (list_paired_values at))
               ~result:(Option.value result ~default:at.result)
               ~substitution)
            with
            old_self = start.self;
          }
        in
        Option.fold ~none:inside ~some:(Lending.bind_final inside) at.final_result
    | Some _ | None -> at
  in
  let trait_requires =
    match inherited with
    | Some (clauses, _) ->
        Logic.conjunction
          (List.map
             (fun requirement ->
               snd (Validity.read_specification context (read_in start clauses) requirement))
             (Facts.list_clauses clauses.requires))
    | None -> Logic.Boolean true
  in
  let mir =
    match Mir.read_code lookups.mir path with
    | Some { form; _ } -> form
    | None -> Facts.raise_bug "`%s` has a body and no MIR" (Resolve.Names.show_key source.key)
  in
  let counts_provider_potential = is_capability_implementation lookups path in
  let promised =
    List.concat_map
      (fun ({ made_by; _ } : Contracts.promise) ->
        Cost_promises.list_promises context made_by.callee (read_in start made_by).locals
          made_by.costs ~inherited:made_by.inherited ~counts_provider_potential)
      promises
  in
  let start = Cost_promises.enter_definition context start promised ~body:(Some mir.body) in
  let declared_requires = Facts.list_clauses own.requires in
  if context.environment.inherits_precondition then
    if declared_requires = [] then Facts.assume start trait_requires
    else
      ignore
        (List.fold_left
           (fun frame (requirement : Mir.formula) ->
             let frame, term =
               Validity.read_specification ~holds_when:requirement.holds_when context frame
                 requirement
             in
             Obligations.oblige ~holds_when:requirement.holds_when frame
               (Facts.locate frame requirement.origin)
               (Impl_precondition { clause = Facts.quote source requirement.origin })
               term;
             frame)
           (Facts.restrict start trait_requires)
           declared_requires);
  (if own.panics_unless <> [] then
     match inherited with
     | Some (clauses, _) when clauses.panics_unless <> [] ->
         let trait_condition =
           Logic.conjunction
             (List.map
                (fun (requirement : Mir.requirement) ->
                  snd
                    (Validity.read_specification context (read_in start clauses) requirement.clause))
                clauses.panics_unless)
         in
         ignore
           (List.fold_left
              (fun frame (requirement : Mir.requirement) ->
                let frame, term = Validity.read_specification context frame requirement.clause in
                Obligations.oblige frame
                  (Facts.locate frame requirement.clause.origin)
                  (Impl_panic_condition { clause = Facts.quote source requirement.clause.origin })
                  term;
                frame)
              (Facts.restrict (Facts.restrict start trait_requires) trait_condition)
              own.panics_unless)
     | Some _ | None -> ());
  let start =
    List.fold_left
      (fun frame (requirement : Mir.formula) ->
        let frame, term = read_requires context frame requirement in
        Facts.assume frame term;
        frame)
      start declared_requires
  in
  let start =
    if assumes_panic_condition then
      List.fold_left
        (fun frame (requirement : Mir.requirement) ->
          let frame, term = Validity.read_specification context frame requirement.clause in
          Facts.assume frame term;
          frame)
        start own.panics_unless
    else start
  in
  Cost_promises.check_promise_amounts context start promised ~output;
  List.iter
    (fun (measure : Mir.formula) ->
      Validity.check_defined context start ~holds_when:measure.holds_when measure)
    measures;
  let returns = List.rev (Reader.read_body context start ~lambdas:mir.lambdas mir.body) in
  let mut_parameters =
    List.filter
      (fun (parameter : Mir.parameter) ->
        parameter.mode = Language.Mode.Mut && parameter.local <> Self)
      parameters
  in
  let mut_self =
    List.exists
      (fun (parameter : Mir.parameter) ->
        parameter.mode = Language.Mode.Mut && parameter.local = Self)
      parameters
  in
  let check_promises (frame : State.frame) location ~is_checked ~moment =
    List.iter
      (fun ({ made_by; proven_under } : Contracts.promise) ->
        let inside = read_in frame made_by
        and under = if proven_under.inherited then Facts.restrict frame trait_requires else frame in
        List.iter
          (fun (ensured : Mir.formula) ->
            if is_checked ensured then
              let _, term =
                Validity.read_specification ~holds_when:ensured.holds_when context inside ensured
              in
              Obligations.oblige ~holds_when:ensured.holds_when
                ~cited:(made_by.callee.key, ensured.origin)
                under location
                (Postcondition
                   {
                     clause = Facts.quote made_by.callee ensured.origin;
                     promiser =
                       (if made_by.inherited then
                          Some (Contracts.find_promiser lookups made_by.callee)
                        else None);
                     moment;
                   })
                term)
          made_by.ensures)
      promises
  in
  List.iter
    (fun ({ lent_frame; lent_origin } : State.lent_part) ->
      let location = Facts.locate lent_frame lent_origin in
      check_promises lent_frame location ~is_checked:Lending.holds_where_lent ~moment:Where_lent)
    (Lending.list_lent_parts context);
  let holds_at_exit clause = not (lends && Lending.holds_where_lent clause) in
  let exit_moment : Catalog.Prover.postcondition_moment =
    if lends then At_lend_end else At_return
  in
  List.iter
    (fun ({ frame; returned; return_origin } : State.function_exit) ->
      let frame = if lends then frame else { frame with result = returned } in
      let exit_location = Facts.locate frame return_origin in
      (match (returned, output) with
      | Some term, Some output ->
          Validity.check_valid context frame exit_location output term ~deep:true
            ~moment:Returned_value
      | _ -> ());
      List.iter
        (fun (parameter : Mir.parameter) ->
          match
            ( Locals.find_opt (Core_local parameter.local) frame.locals,
              Encoding.find_local_type frame (Core_local parameter.local) )
          with
          | Some term, Some ty ->
              Validity.check_valid context frame exit_location ty term ~deep:true
                ~moment:(Mut_parameter_at_return (Facts.read_parameter_name parameter))
          | _ -> ())
        mut_parameters;
      (match (mut_self, frame.self, frame.self_type) with
      | true, Some self, Some self_type ->
          Validity.check_valid context frame exit_location self_type self ~deep:true
            ~includes_invariants:(not is_update_step) ~moment:Self_at_return
      | _ -> ());
      check_promises frame exit_location ~is_checked:holds_at_exit ~moment:exit_moment;
      let under_trait = Facts.restrict frame trait_requires in
      List.iter
        (fun (promise : Cost_promises.promise) ->
          let cited = (promise.written_in.key, promise.clause.origin) in
          if promise.inherited then
            let inside = read_in ~result:returned frame (fst (Option.get inherited)) in
            Cost_promises.check_promise ~cited context under_trait promise
              ~at:{ inside with locals = inside.old_locals; self = inside.old_self }
              ~location:exit_location
          else
            Cost_promises.check_promise ~cited context frame promise
              ~at:{ frame with locals = frame.old_locals; self = frame.old_self; result = returned }
              ~location:exit_location)
        promised)
    returns;
  (make_outcome context, context.skipped_conditions)

let find_circular_contract (lookups : Lookups.t) (source : State.source) ~path =
  let context =
    make_context lookups ~home:source.key ~current:path ~terminates:false ~measures:[]
      ~inherits_precondition:false
  in
  let start = make_empty_frame context.environment context.query source in
  match Cycles.list_circular_contracts start with
  | [] -> None
  | circular ->
      List.iter (Cycles.reject_circular_proof start) circular;
      Some (make_outcome context)

let find_circular_laws (lookups : Lookups.t) (source : State.source) ~path =
  let context =
    make_context lookups ~home:source.key ~current:path ~terminates:false ~measures:[]
      ~inherits_precondition:false
  in
  let start = make_empty_frame context.environment context.query source in
  match Cycles.list_circular_laws start with
  | [] -> None
  | circular ->
      List.iter (Cycles.reject_circular_proof start) circular;
      Some (make_outcome context)

let translate_function ?(substitution = Types.no_substitution) (lookups : Lookups.t)
    (source : State.source) ~path =
  match find_circular_contract lookups source ~path with
  | Some outcome -> outcome
  | None ->
      let run ?(assumes_panic_condition = false) condition =
        translate_run ~substitution ~condition ~assumes_panic_condition lookups source ~path
      in
      let base, skipped = run [] in
      let has_panic_condition =
        match Interface.Impls.read_signature lookups.interface path with
        | Some signature ->
            Types.has_capability (Capability_unless_values (Built_in Panic)) signature.uses
        | None -> false
      in
      let find_capability_condition capability =
        match Interface.Impls.read_signature lookups.interface path with
        | Some signature when not (Types.has_capability capability signature.uses) ->
            Option.to_list
              (Types.find_unless capability
                 (Types.substitute_capabilities substitution signature.uses))
        | Some _ | None -> []
      in
      let outcomes =
        base
        :: (if has_panic_condition then [ fst (run ~assumes_panic_condition:true []) ] else [])
        @ List.map
            (fun condition -> fst (run condition))
            (List.sort_uniq compare
               (find_capability_condition (Built_in Run_forever)
               @ find_capability_condition (Built_in Panic)
               @ skipped))
      in
      {
        Obligation.obligations =
          List.concat_map (fun (outcome : Obligation.outcome) -> outcome.obligations) outcomes;
        holes =
          List.sort_uniq compare
            (List.concat_map (fun (outcome : Obligation.outcome) -> outcome.holes) outcomes);
        evaluation = None;
      }

let translate_laws (lookups : Lookups.t) (source : State.source) ~impl ~trait ~for_type ~proofs ~at
    =
  let home = source.key in
  let context =
    make_context lookups ~home ~current:impl ~terminates:false ~measures:[]
      ~inherits_precondition:false ~proven_laws:(trait, for_type)
  in
  let start = make_empty_frame context.environment context.query source in
  let substitution = Contracts.make_trait_substitution lookups trait for_type in
  List.iter
    (fun (law_source, (law : Mir.law)) ->
      let types = Laws.list_law_parameter_types ~substitution law in
      if not (List.exists (fun ty -> Types.is_error ty) types) then begin
        let terms =
          List.map
            (fun ty ->
              let term = Encoding.arrive start "law" ty in
              Validity.assume_valid context start ty term;
              term)
            types
        in
        let inside = Laws.bind_law_parameters start law_source ~substitution law terms in
        List.iter
          (fun clause ->
            Facts.assume start (snd (Validity.read_specification context inside clause)))
          law.requires;
        let start =
          List.fold_left
            (fun (start : State.frame) ((proof_source : State.source), renaming) ->
              let proof =
                match Mir.find_code (lookups.mir.read_body_part proof_source.key) with
                | Some proof -> proof
                | None ->
                    Facts.raise_bug "the proof `%s` has no MIR"
                      (Resolve.Names.show_key proof_source.key)
              in
              let parameters =
                List.map
                  (fun parameter ->
                    match proof.body.locals.(parameter) with
                    | { kind = Source { local; _ }; type_; _ } -> (local, type_)
                    | { kind = Temporary | Lent _; _ } ->
                        Facts.raise_bug "a parameter of the proof `%s` is a temporary"
                          (Resolve.Names.show_key proof_source.key))
                  proof.body.parameters
              in
              let locals, types =
                List.fold_left2
                  (fun (locals, types) (local, type_) term ->
                    ( Locals.add (Core_local local) term locals,
                      Locals.add (Core_local local) (Types.substitute_erased renaming type_) types
                    ))
                  (start.locals, start.types) parameters
                  (List.take (List.length parameters) terms)
              in
              Facts.restrict start
                (Logic.not_
                   (Values.run_ghost_code context
                      {
                        start with
                        source = proof_source;
                        makes_obligations = false;
                        locals;
                        types;
                        substitution = renaming;
                      }
                      proof)))
            start
            (List.filter_map
               (fun (name, proof) -> if name = law.name then Some proof else None)
               proofs)
        in
        let _, holds = Validity.read_specification context inside law.states in
        Obligations.oblige start at (Law_may_fail { trait; law = law.name; for_type }) holds
      end)
    (Laws.list_laws context.environment trait.trait);
  make_outcome context

let prove_restated_method (context : State.context) (start : State.frame) ~at ~impl_interface ~trait
    ~for_type (restated : Types.restated_method) (clauses : State.clauses) =
  let lookups = context.environment.lookups in
  let name = restated.restated_name and receiver = restated.restated_receiver in
  let restated_path = Path.Method { owner = trait.Types.trait; name; receiver } in
  let list_bounds =
    Interface.Properties.Bounds.close lookups.interface
      (Types.list_bounds impl_interface.Types.impl_generics)
  in
  let declared =
    match Contracts.find_restated_trait lookups ~self_type:for_type trait restated with
    | Some declared -> declared
    | None ->
        Facts.raise_bug "`%s` restates a method of `%s`, which it does not require"
          (Path.show trait.trait) (Path.show restated.declared_by)
  in
  match Interface.Impls.find_evidence lookups.interface ~list_bounds for_type declared with
  | Some (Evidence (Impl { impl; substitution } | Derived_for_view { viewed = impl; substitution }))
    -> (
      let evidence : Types.evidence = Impl { impl; substitution } in
      let signature =
        match Interface.Impls.read_signature lookups.interface restated_path with
        | Some signature -> signature
        | None ->
            Facts.raise_bug "the restated method `%s` has no signature" (Path.show restated_path)
      in
      let subtrait_substitution = Contracts.make_trait_substitution lookups trait for_type in
      let callee =
        Callee.resolve start
          (Trait_method
             {
               trait = declared;
               name;
               receiver;
               self_type = for_type;
               instantiation =
                 {
                   type_arguments =
                     List.map
                       (fun (generic : Types.generic) ->
                         Types.Type (Types.Parameter generic.generic))
                       signature.generics;
                   capability_arguments = [];
                 };
               evidence;
             })
          ~lends:(match signature.output with Lends (mode, _) -> Some mode | Returns _ -> None)
          ~uses:(Types.substitute_capabilities subtrait_substitution signature.uses)
      in
      match callee.target with
      | Function_value | Intrinsic _ | Definition { contract = None; _ } ->
          Facts.raise_bug "the method that `%s` restates has no contract" (Path.show restated_path)
      | Definition ({ contract = Some contract; _ } as definition) ->
          let contract = { contract with restated_clauses = [] } in
          let read_place (parameter : Mir.parameter) (frame : State.frame) =
            match parameter.local with
            | Self -> Option.get frame.self
            | local -> Option.get (Locals.find_opt (Core_local local) frame.locals)
          and write_place (parameter : Mir.parameter) (frame : State.frame) term =
            match parameter.local with
            | Self -> { frame with self = Some term }
            | local -> { frame with locals = Locals.add (Core_local local) term frame.locals }
          in
          let entry =
            List.fold_left
              (fun (frame : State.frame) (parameter : Mir.parameter) ->
                let ty = Types.substitute_erased subtrait_substitution parameter.type_ in
                let term =
                  Encoding.arrive frame ("parameter." ^ Facts.read_parameter_name parameter) ty
                in
                Validity.assume_valid context frame ty term;
                write_place parameter frame term)
              start clauses.parameters
          in
          let list_arguments (frame : State.frame) =
            List.mapi
              (fun position parameter -> (position, read_place parameter frame))
              clauses.parameters
          in
          let reading (frame : State.frame) =
            Contracts.make_entry_frame frame clauses ~arguments:(list_arguments frame)
              ~substitution:subtrait_substitution
          in
          let promised =
            Cost_promises.list_promises context clauses.callee (reading entry).locals clauses.costs
              ~inherited:true ~counts_provider_potential:false
          in
          let entry = Cost_promises.enter_definition context entry promised ~body:None in
          let result_type =
            Types.substitute_erased subtrait_substitution
              (Types.extract_result_type signature.output)
          in
          let ({ frame = lent; result; end_lend } : Calls.applied) =
            Calls.call_contract context entry
              { origin = at; type_ = result_type }
              callee definition contract
              (List.mapi
                 (fun position (parameter : Mir.parameter) : State.passed ->
                   {
                     position;
                     mode = parameter.mode;
                     origin = None;
                     passed_place =
                       (match parameter.mode with
                       | Language.Mode.Mut ->
                           Some
                             {
                               read = read_place parameter;
                               write =
                                 (fun frame ~is_valid:_ term ->
                                   (write_place parameter frame term, ignore));
                             }
                       | Read | Own -> None);
                     type_ = Types.substitute_erased subtrait_substitution parameter.type_;
                     is_step_self = false;
                     declared_type = Types.substitute subtrait_substitution parameter.type_;
                     term = read_place parameter entry;
                   })
                 clauses.parameters)
              ~recursive_callee:None
          in
          let entry_reading = reading entry and location = Facts.locate start at in
          let check_restated (after : State.frame) ~final ~is_checked =
            let ensuring =
              {
                (reading after) with
                old_locals = entry_reading.locals;
                old_self = entry_reading.self;
                result = Some result;
              }
            in
            let ensuring =
              match final with Some final -> Lending.bind_final ensuring final | None -> ensuring
            in
            List.iter
              (fun (clause : Mir.formula) ->
                if is_checked clause then
                  let _, term = Validity.read_specification context ensuring clause in
                  Obligations.oblige after location
                    (Restated_contract
                       {
                         for_type;
                         name;
                         clause = Facts.quote clauses.callee clause.origin;
                         trait;
                         declared;
                       })
                    term)
              clauses.ensures
          in
          let after =
            match signature.output with
            | Returns _ ->
                check_restated lent ~final:None ~is_checked:(fun _ -> true);
                lent
            | Lends _ ->
                check_restated lent ~final:None ~is_checked:Lending.holds_where_lent;
                let final, after =
                  match end_lend with
                  | Some end_lend ->
                      let final = Encoding.arrive lent "final" result_type in
                      Validity.assume_valid context lent result_type final;
                      (final, end_lend lent final)
                  | None -> (result, lent)
                in
                check_restated after ~final:(Some final) ~is_checked:(fun clause ->
                    not (Lending.holds_where_lent clause));
                after
          in
          List.iter
            (fun promise ->
              Cost_promises.check_promise context after promise ~at:entry_reading ~location
                ~restated:(for_type, name, trait, declared))
            promised)
  | Some Built_in ->
      Facts.raise_unsupported (Facts.locate start at)
        (Compiler_restated_method { trait; declared_by = restated.declared_by })
  | Some (Evidence Bound) ->
      Facts.raise_bug "`%s` implements `%s` through a bound" (Types.show for_type)
        (Types.show_trait declared)
  | Some (Accepted _) | None -> ()

let translate_restated_clauses (lookups : Lookups.t) (source : State.source) ~impl ~trait ~for_type
    ~at =
  run_blocking @@ fun ?blocked_holders () ->
  let home = source.key in
  let context =
    make_context lookups ?blocked_holders ~home ~current:impl ~terminates:false ~measures:[]
      ~inherits_precondition:false
  in
  let impl_interface = Interface.Definition.read_impl_interface lookups.interface impl in
  List.iter
    (fun (restated : Types.restated_method) ->
      let path =
        Path.Method
          {
            owner = trait.Types.trait;
            name = restated.restated_name;
            receiver = restated.restated_receiver;
          }
      in
      match Contracts.find_declared_clauses lookups path with
      | Some clauses ->
          prove_restated_method context
            (make_empty_frame context.environment context.query source)
            ~at ~impl_interface ~trait ~for_type restated clauses
      | None -> Facts.raise_bug "the restated method `%s` has no contract" (Path.show path))
    (Interface.Definition.read_trait_interface lookups.interface trait.trait).restated;
  make_outcome context

let translate_type (lookups : Lookups.t) (source : State.source) ~path =
  let home = source.key in
  let context =
    make_context lookups ~home ~current:path ~terminates:false ~measures:[]
      ~inherits_precondition:false
  in
  (match Mir.read_type_clauses lookups.mir path with
  | Some { form = { invariants; potential }; _ } -> (
      let ty =
        match Interface.Definition.find_interface lookups.interface path with
        | Some (Interface.Environment.Type_interface interface) ->
            Types.Named { path; arguments = Types.list_generic_arguments interface.type_generics }
        | _ -> Facts.raise_bug "%s is not a type" (Path.show path)
      in
      let start =
        { (make_empty_frame context.environment context.query source) with self_type = Some ty }
      in
      (match Mir.read_defaults lookups.mir path with
      | Some { form = Field_defaults defaults; _ } ->
          List.iter
            (fun (default : Mir.t Mir.field_default) ->
              ignore
                (Lambdas.run_code context start default.value
                   ~type_:(Encoding.substitute_type start default.type_)))
            defaults
      | Some { form = Parameter_defaults _; _ } | None -> ());
      match Cycles.list_circular_clauses start ~type_:ty with
      | _ :: _ as circular -> List.iter (Cycles.reject_circular_proof start) circular
      | [] ->
          let value_ = Encoding.arrive start "value" ty in
          Facts.assume start
            (Validity.make_validity context start ~assuming:true ~includes_invariants:false ty
               value_);
          let at_value = { start with self = Some value_; old_self = Some value_ } in
          List.iter
            (fun (invariant : Mir.requirement) ->
              let after, holds = Validity.read_specification context at_value invariant.clause in
              Facts.assume after holds)
            invariants;
          Option.iter
            (fun (written : Mir.formula) ->
              let _, potential_term = Validity.read_specification context at_value written in
              Obligations.oblige at_value
                (Facts.locate at_value written.origin)
                (Negative_potential { type_ = ty })
                (Logic.less_equal (Logic.int 0) potential_term))
            potential)
  | None -> ());
  make_outcome context

let translate_constant (lookups : Lookups.t) (source : State.source) ~path =
  let home = source.key in
  let context =
    make_context lookups ~home ~current:path ~terminates:false ~measures:[]
      ~inherits_precondition:false
  in
  match Mir.read_initializer lookups.mir path with
  | Some { form = code; _ } ->
      let frame = make_empty_frame context.environment context.query source in
      Cycles.reject_constant_cycle frame code;
      ignore
        (Lambdas.run_code context frame code
           ~type_:
             (Interface.Definition.read_constant_type context.environment.lookups.interface path));
      {
        (make_outcome context) with
        evaluation =
          (if Cycles.is_evaluated_constant context.environment path code then
             Some (Constant_value path)
           else None);
      }
  | None -> Facts.raise_bug "the constant `%s` has no MIR" (Path.show path)
