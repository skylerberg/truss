let make_environment ?node ?(condition = []) ?(keeps_termination = true) ?(keeps_failures = true)
    ?panic_condition ?blocked_holders ?proven_laws (lookups : Lookups.t) ~home ~current ~terminates
    ~measures ~inherits_precondition =
  let node = Option.value node ~default:current in
  let inductive_heads = Cycles.list_inductive_heads lookups node in
  {
    State.lookups;
    current;
    node;
    home;
    condition;
    bounds = Encoding.list_definition_bounds lookups ~current ~condition;
    disjoint = lookups.list_must_be_disjoint home;
    inherits_precondition;
    ranking =
      (terminates && measures = [] && lookups.list_recursion_group node <> [])
      || inductive_heads <> [];
    terminates;
    measures;
    termination = lazy (lookups.find_termination node);
    blocked_holders = Option.value blocked_holders ~default:[];
    proven_laws;
    inductive_heads;
    policy = Obligations.make_policy ~keeps_termination ~keeps_failures ~panic_condition;
    memos = Private_state.create ();
    read_formula = Reader.read_formula;
    run_body = Reader.read_body;
  }

let make_outcome (query : Query.t) =
  {
    Obligation.obligations = Query.list_obligations query;
    holes = Query.list_holes query;
    evaluated_constants = [];
  }

let merge_outcomes (outcomes : Obligation.outcome list) : Obligation.outcome =
  {
    obligations =
      List.concat_map (fun (outcome : Obligation.outcome) -> outcome.obligations) outcomes;
    holes =
      List.sort_uniq compare
        (List.concat_map (fun (outcome : Obligation.outcome) -> outcome.holes) outcomes);
    evaluated_constants =
      List.concat_map (fun (outcome : Obligation.outcome) -> outcome.evaluated_constants) outcomes;
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
    lent_part_type = None;
    definition_entry = None;
    visited = None;
    final_result = None;
    spent = [];
    conditional_counters = [];
  }

let start_proof ?blocked_holders ?proven_laws (lookups : Lookups.t) (source : State.source) ~current
    =
  make_empty_frame
    (make_environment lookups ?blocked_holders ?proven_laws ~home:source.key ~current
       ~terminates:false ~measures:[] ~inherits_precondition:false)
    (Query.create ()) source

let is_capability_implementation (lookups : Lookups.t) (path : Path.t) =
  match path with
  | Method { owner; _ } -> (
      match Interface.Definition.find_impl_interface lookups.interface owner with
      | Some impl ->
          Resolve.Names.find_kind lookups.interface.names impl.implements.trait
          = Some Resolve.Names.Capability
      | None -> false)
  | _ -> false

let read_requires (frame : State.frame) (requirement : Mir.formula) =
  let after, term =
    Validity.read_specification ~holds_when:requirement.holds_when
      { frame with requires_being_read = Some requirement.origin }
      requirement
  in
  ({ after with requires_being_read = frame.requires_being_read }, term)

let rec run_blocking ?blocked_holders translate =
  try translate ?blocked_holders ()
  with Counters.Blocks_credited_potential blocked_holders ->
    run_blocking ~blocked_holders translate

let bind_parameters (empty : State.frame) (parameters : Mir.parameter list) ~is_update_step =
  let bound =
    List.fold_left
      (fun frame (parameter : Mir.parameter) ->
        let ty = Encoding.substitute_type frame parameter.type_ in
        match parameter.local with
        | Self ->
            let self = Encoding.arrive frame "self" ty in
            Validity.assume_valid frame ~includes_invariants:(not is_update_step) ty self;
            { (note_entry frame self ~name:None) with self = Some self; self_type = Some ty }
        | local ->
            let name = Facts.read_parameter_name parameter in
            let term = Encoding.arrive frame ("parameter." ^ name) ty in
            Validity.assume_valid frame ty term;
            Facts.bind (note_entry frame term ~name:(Some name)) (Core_local local) ty term)
      empty parameters
  in
  { bound with old_locals = bound.locals; old_self = bound.self }

let read_parameter (parameter : Mir.parameter) (at : State.frame) =
  match
    match parameter.local with
    | Self -> at.self
    | local -> Locals.find_opt (Core_local local) at.locals
  with
  | Some term -> term
  | None ->
      Facts.raise_bug "the parameter `%s` of `%s` has no value"
        (Facts.read_parameter_name parameter)
        (Resolve.Names.show_key at.source.key)

let list_parameter_values (parameters : Mir.parameter list) (at : State.frame) =
  List.map (fun parameter -> read_parameter parameter at) parameters

let bind_parameter_values (entry : State.frame) (clauses : State.clauses) ~substitution ~list_values
    ?result (at : State.frame) =
  let number terms = List.mapi (fun position term -> (position, term)) terms in
  let inside =
    {
      (Contracts.make_exit_frame at clauses
         ~entries:(number (list_values entry))
         ~exits:(number (list_values at))
         ~result:(Option.value result ~default:at.result)
         ~substitution)
      with
      old_self = entry.self;
    }
  in
  Option.fold ~none:inside ~some:(Lending.bind_final inside) at.final_result

let assume_precondition (start : State.frame) (source : State.source) ~(own : State.clauses)
    ~(inherited : (State.clauses * State.frame) option) ~trait_requires =
  let declared_requires = Facts.list_clauses own.requires in
  let assume_own () =
    List.fold_left
      (fun frame (requirement : Mir.formula) ->
        let frame, term = read_requires frame requirement in
        Facts.assume frame term;
        frame)
      start declared_requires
  in
  match (inherited, declared_requires) with
  | Some _, [] when start.environment.inherits_precondition ->
      Facts.assume start trait_requires;
      start
  | Some (trait_clauses, inside), restated :: _ when start.environment.inherits_precondition ->
      ignore
        (List.fold_left
           (fun frame (requirement : Mir.formula) ->
             let frame, term =
               Validity.read_specification ~holds_when:requirement.holds_when frame requirement
             in
             Obligations.oblige ~holds_when:requirement.holds_when frame
               (Facts.locate frame requirement.origin)
               (Impl_precondition { clause = Facts.quote source requirement.origin })
               term;
             frame)
           (Facts.restrict start trait_requires)
           declared_requires);
      let assumed = assume_own () in
      List.iter
        (fun (requirement : Mir.formula) ->
          Obligations.oblige assumed
            (Facts.locate assumed restated.origin)
            (Trait_precondition { clause = Facts.quote trait_clauses.callee requirement.origin })
            (snd (Validity.read_specification inside requirement)))
        (Facts.list_clauses trait_clauses.requires);
      assumed
  | (Some _ | None), _ -> assume_own ()

let check_panic_condition_against_the_trait (start : State.frame) (source : State.source)
    ~(own : State.clauses) ~(inherited : (State.clauses * State.frame) option) ~trait_requires =
  if own.panics_unless <> [] then
    match inherited with
    | Some (clauses, inside) when clauses.panics_unless <> [] ->
        let trait_condition =
          Logic.conjunction
            (List.map
               (fun (requirement : Mir.requirement) ->
                 snd (Validity.read_specification inside requirement.clause))
               clauses.panics_unless)
        in
        ignore
          (List.fold_left
             (fun frame (requirement : Mir.requirement) ->
               let frame, term = Validity.read_specification frame requirement.clause in
               Obligations.oblige frame
                 (Facts.locate frame requirement.clause.origin)
                 (Impl_panic_condition { clause = Facts.quote source requirement.clause.origin })
                 term;
               frame)
             (Facts.restrict (Facts.restrict start trait_requires) trait_condition)
             own.panics_unless)
    | Some _ | None -> ()

type case = {
  clauses : State.clauses;
  costs : Cost_promises.promise list;
  bind_values : ?result:Logic.term option -> State.frame -> State.frame;
}

type entered_function = {
  start : State.frame;
  cases : case list;
  code : Mir.t;
  parameters : Mir.parameter list;
  output : Types.ty option;
  is_update_step : bool;
}

type run = {
  environment : State.environment;
  signature : Types.signature option;
  is_update_step : bool;
  is_specification_only : bool;
  panics : bool;
  can_declare_panic : bool;
}

let make_run ~substitution ~condition ~assumes_panic_condition ?blocked_holders
    (lookups : Lookups.t) (source : State.source) ~path (contract : Mir.contract) =
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
  let environment =
    make_environment lookups ~condition ~keeps_termination ~keeps_failures ?panic_condition
      ?blocked_holders ~home ~current:path
      ~node:
        (Mir.Call_edges.resolve_node
           { interface = lookups.interface; mir = lookups.mir }
           path substitution)
      ~terminates ~measures
      ~inherits_precondition:
        (Option.is_some (Interface.Impls.find_implemented_method lookups.interface path))
  in
  { environment; signature; is_update_step; is_specification_only; panics; can_declare_panic }

let resolve_clause_sets (environment : State.environment) (query : Query.t) (source : State.source)
    ~path (contract : Mir.contract) =
  List.iter
    (fun (measure : Mir.formula) ->
      ignore
        (Conditions.decide environment query ~substitution:Types.no_substitution measure.holds_when))
    contract.decreases;
  let keep_clauses = Conditions.keep_holding environment query in
  let keep_inherited (clauses, substitution) = (keep_clauses ~substitution clauses, substitution) in
  let inherited = Option.map keep_inherited (Contracts.find_inherited_clauses environment path) in
  let added = List.map keep_inherited (Contracts.list_added_clauses environment path) in
  let own, clause_sets =
    match Contracts.find_function_contract environment path with
    | Some resolved ->
        let own =
          keep_clauses ~substitution:Types.no_substitution
            { resolved.callee_clauses with callee = source }
        in
        ( own,
          Contracts.list_clause_sets
            {
              resolved with
              callee_clauses = own;
              trait_clauses = Option.map fst inherited;
              restated_clauses = List.map fst added;
            } )
    | None -> Facts.raise_bug "`%s` has no contract" (Resolve.Names.show_key source.key)
  in
  (own, inherited, added, clause_sets)

let bind_entry (run : run) (query : Query.t) (source : State.source) ~path ~substitution ~condition
    (contract : Mir.contract) =
  let { environment; signature; is_update_step; is_specification_only; panics; can_declare_panic } =
    run
  in
  let lookups = environment.lookups and parameters = contract.parameters in
  let output = match signature with Some { output = Returns ty; _ } -> Some ty | _ -> None in
  let start =
    bind_parameters
      {
        (make_empty_frame environment query source) with
        substitution;
        is_ghost = is_specification_only;
        panics;
        can_declare_panic;
      }
      parameters ~is_update_step
  in
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
  let start = Termination.enter_definition start ~parameters in
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
         && lookups.may_abort environment.node
         && Types.states_no_allocation declared.costs ->
      Obligations.oblige start Whole_definition (May_not_return_under_no_allocation This_method)
        (Logic.Boolean false)
  | Some _ | None -> ());
  let output = Option.map (Encoding.substitute_type start) output in
  let start =
    match signature with
    | Some { output = Lends (_, part); _ } ->
        { start with lent_part_type = Some (Encoding.substitute_type start part) }
    | Some { output = Returns _; _ } | None -> start
  in
  (start, output)

let enter_function ~substitution ~condition ~assumes_panic_condition ?blocked_holders
    (lookups : Lookups.t) (source : State.source) ~path (query : Query.t) =
  let contract =
    match Mir.read_contract lookups.mir path with
    | Some { form; _ } -> form
    | None -> Facts.raise_bug "`%s` has no MIR of its contract" (Resolve.Names.show_key source.key)
  in
  let parameters = contract.parameters in
  let run =
    make_run ~substitution ~condition ~assumes_panic_condition ?blocked_holders lookups source ~path
      contract
  in
  let environment = run.environment in
  let own, inherited, added, clause_sets =
    resolve_clause_sets environment query source ~path contract
  in
  let pair_up (clauses : State.clauses) terms =
    match (parameters, terms) with
    | { local = Self; _ } :: _, _ :: rest
      when not
             (List.exists
                (fun (parameter : Mir.parameter) -> parameter.local = Self)
                clauses.parameters) ->
        rest
    | _ -> terms
  in
  let start, output = bind_entry run query source ~path ~substitution ~condition contract in
  let entry = start in
  let substitutions =
    List.map
      (fun ((clauses : State.clauses), substitution) -> (clauses.callee.key, substitution))
      (Option.to_list inherited @ added)
  in
  let bind_values (clauses : State.clauses) =
    match List.assoc_opt clauses.callee.key substitutions with
    | Some substitution ->
        bind_parameter_values entry clauses ~substitution ~list_values:(fun at ->
            pair_up clauses (list_parameter_values parameters at))
    | None -> (
        fun ?result (at : State.frame) ->
          match result with Some result -> { at with result } | None -> at)
  in
  let inherited =
    Option.map
      (fun ((clauses : State.clauses), _) -> (clauses, bind_values clauses entry))
      inherited
  in
  let trait_requires =
    match inherited with
    | Some (clauses, inside) ->
        Logic.conjunction
          (List.map
             (fun requirement -> snd (Validity.read_specification inside requirement))
             (Facts.list_clauses clauses.requires))
    | None -> Logic.Boolean true
  in
  let mir =
    match Mir.read_code lookups.mir path with
    | Some { form; _ } -> form
    | None -> Facts.raise_bug "`%s` has a body and no MIR" (Resolve.Names.show_key source.key)
  in
  let counts_provider_potential = is_capability_implementation lookups path in
  let cases =
    List.map
      (fun (clauses : State.clauses) ->
        {
          clauses;
          costs =
            Cost_promises.list_promises environment query clauses.callee
              (bind_values clauses entry).locals clauses.costs ~inherited:clauses.inherited
              ~counts_provider_potential;
          bind_values = bind_values clauses;
        })
      clause_sets
  in
  let promised = List.concat_map (fun case -> case.costs) cases in
  let start = Cost_promises.enter_definition start promised ~body:(Some mir.body) in
  check_panic_condition_against_the_trait start source ~own ~inherited ~trait_requires;
  let start = assume_precondition start source ~own ~inherited ~trait_requires in
  let start =
    if assumes_panic_condition then
      List.fold_left
        (fun frame (requirement : Mir.requirement) ->
          let frame, term = Validity.read_specification frame requirement.clause in
          Facts.assume frame term;
          frame)
        start own.panics_unless
    else start
  in
  Cost_promises.check_promise_amounts start promised ~output;
  List.iter
    (fun (measure : Mir.formula) ->
      Validity.check_defined start ~holds_when:measure.holds_when measure)
    environment.measures;
  { start; cases; code = mir; parameters; output; is_update_step = run.is_update_step }

let check_ensures entered (frame : State.frame) location ~is_checked ~moment =
  List.iter
    (fun case ->
      let inside = case.bind_values frame in
      List.iter
        (fun (ensured : Mir.formula) ->
          if is_checked ensured then
            let _, term =
              Validity.read_specification ~holds_when:ensured.holds_when inside ensured
            in
            Obligations.oblige ~holds_when:ensured.holds_when
              ~cited:(case.clauses.callee.key, ensured.origin)
              frame location
              (Postcondition
                 {
                   clause = Facts.quote case.clauses.callee ensured.origin;
                   promiser =
                     (if case.clauses.inherited then
                        Some (Contracts.find_promiser case.clauses.callee)
                      else None);
                   moment;
                 })
              term)
        case.clauses.ensures)
    entered.cases

let check_lent_part entered ({ lent_frame; lent_origin } : State.lent_part) =
  check_ensures entered lent_frame
    (Facts.locate lent_frame lent_origin)
    ~is_checked:Lending.holds_where_lent ~moment:Where_lent

let bind_returned entered (exit_ : State.function_exit) : State.function_exit =
  if Option.is_some entered.start.lent_part_type then exit_
  else { exit_ with frame = { exit_.frame with result = exit_.returned } }

let check_returned_values entered ({ frame; returned; return_origin } : State.function_exit) =
  let exit_location = Facts.locate frame return_origin in
  (match (returned, entered.output) with
  | Some term, Some output ->
      Validity.check_valid frame exit_location output term ~deep:true ~moment:Returned_value
  | _ -> ());
  let is_mut (parameter : Mir.parameter) = parameter.mode = Language.Mode.Mut in
  let mut_self, mut_parameters =
    List.partition
      (fun (parameter : Mir.parameter) -> parameter.local = Self)
      (List.filter is_mut entered.parameters)
  in
  List.iter
    (fun (parameter : Mir.parameter) ->
      match
        ( Locals.find_opt (Core_local parameter.local) frame.locals,
          Encoding.find_local_type frame (Core_local parameter.local) )
      with
      | Some term, Some ty ->
          Validity.check_valid frame exit_location ty term ~deep:true
            ~moment:(Mut_parameter_at_return (Facts.read_parameter_name parameter))
      | _ -> ())
    mut_parameters;
  match (mut_self, frame.self, frame.self_type) with
  | _ :: _, Some self, Some self_type ->
      Validity.check_valid frame exit_location self_type self ~deep:true
        ~includes_invariants:(not entered.is_update_step) ~moment:Self_at_return
  | _ -> ()

let check_return entered ({ frame; returned; return_origin } : State.function_exit) =
  let lends = Option.is_some entered.start.lent_part_type in
  let exit_location = Facts.locate frame return_origin in
  check_ensures entered frame exit_location
    ~is_checked:(fun clause -> not (lends && Lending.holds_where_lent clause))
    ~moment:(if lends then At_lend_end else At_return);
  List.iter
    (fun case ->
      let inside = case.bind_values ~result:returned frame in
      List.iter
        (fun (promise : Cost_promises.promise) ->
          Cost_promises.check_promise
            ~cited:(promise.written_in.key, promise.clause.origin)
            frame promise
            ~at:{ inside with locals = inside.old_locals; self = inside.old_self }
            ~location:exit_location)
        case.costs)
    entered.cases

let translate_run ~substitution ~condition ~assumes_panic_condition (lookups : Lookups.t)
    (source : State.source) ~path =
  run_blocking @@ fun ?blocked_holders () ->
  let query = Query.create () in
  let entered =
    enter_function ~substitution ~condition ~assumes_panic_condition ?blocked_holders lookups source
      ~path query
  in
  let exits = Reader.read_body entered.start ~lambdas:entered.code.lambdas entered.code.body in
  Termination.reject_unreached_calls_without_decrease entered.start;
  List.iter (check_lent_part entered) (List.rev exits.lends);
  List.iter
    (fun returned ->
      let returned = bind_returned entered returned in
      check_returned_values entered returned;
      check_return entered returned)
    (List.rev exits.returns);
  (make_outcome query, Conditions.list_undecided query)

let find_circular_proof (lookups : Lookups.t) (source : State.source) ~path =
  let start = start_proof lookups source ~current:path in
  match Cycles.list_circular_proofs start with
  | [] -> None
  | circular ->
      List.iter (Cycles.reject_circular_proof start) circular;
      Some (make_outcome start.query)

let translate_function ?(substitution = Types.no_substitution) (lookups : Lookups.t)
    (source : State.source) ~path =
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
          (Types.find_unless capability (Types.substitute_capabilities substitution signature.uses))
    | Some _ | None -> []
  in
  let outcomes =
    (base :: (if has_panic_condition then [ fst (run ~assumes_panic_condition:true []) ] else []))
    @ List.map
        (fun condition ->
          let outcome = fst (run condition) in
          {
            outcome with
            obligations =
              List.map
                (fun (obligation : Obligation.t) ->
                  { obligation with instance = { obligation.instance with condition } })
                outcome.obligations;
          })
        (List.sort_uniq compare
           (find_capability_condition (Built_in Run_forever)
           @ find_capability_condition (Built_in Panic)
           @ skipped))
  in
  merge_outcomes outcomes

let prove_law (start : State.frame) ~substitution ~trait ~for_type ~proofs ~at
    ((law_source : State.source), (law : Mir.law)) =
  let lookups = start.environment.lookups in
  let types = Laws.list_law_parameter_types ~substitution law in
  if not (List.exists (fun ty -> Types.is_error ty) types) then begin
    let terms =
      List.map
        (fun ty ->
          let term = Encoding.arrive start "law" ty in
          Validity.assume_valid start ty term;
          term)
        types
    in
    let start =
      if start.environment.inductive_heads = [] then start
      else
        {
          start with
          definition_entry =
            Some
              {
                entry_measures = [];
                entry_ranks = [];
                induction_bound =
                  Termination.find_induction_bound start
                    (List.mapi
                       (fun position (type_, value) -> { State.position; type_; value })
                       (List.combine types terms));
              };
        }
    in
    let inside = Laws.bind_law_parameters start law_source ~substitution law terms in
    List.iter
      (fun clause -> Facts.assume start (snd (Validity.read_specification inside clause)))
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
                  Locals.add (Core_local local) (Types.substitute_erased renaming type_) types ))
              (start.locals, start.types) parameters
              (List.take (List.length parameters) terms)
          in
          Facts.restrict start
            (Logic.not_
               (Values.run_ghost_code
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
        (List.filter_map (fun (name, proof) -> if name = law.name then Some proof else None) proofs)
    in
    let _, holds = Validity.read_specification inside law.states in
    Obligations.oblige start at (Law_may_fail { trait; law = law.name; for_type }) holds
  end

let translate_laws (lookups : Lookups.t) (source : State.source) ~impl ~trait ~for_type ~proofs ~at
    =
  let start_laws () = start_proof lookups source ~current:impl ~proven_laws:(trait, for_type) in
  let start = start_laws () in
  let substitution = Contracts.make_trait_substitution lookups trait for_type in
  let laws = Laws.list_laws start.environment trait.trait in
  let prove start law = prove_law start ~substitution ~trait ~for_type ~proofs ~at law in
  if start.environment.inductive_heads = [] then begin
    List.iter (prove start) laws;
    make_outcome start.query
  end
  else
    merge_outcomes
      (List.mapi
         (fun index law ->
           let start = if index = 0 then start else start_laws () in
           prove start law;
           make_outcome start.query)
         laws)

let is_generic_owner (lookups : Lookups.t) (owner : Path.t) =
  match Interface.Definition.find_interface lookups.interface owner with
  | Some (Type_interface type_interface) -> type_interface.type_generics <> []
  | _ -> (
      (match owner with
        | Method { owner = container; _ } -> (
            match Interface.Definition.find_interface lookups.interface container with
            | Some (Trait_interface _) -> true
            | _ -> false)
        | _ -> false)
      ||
      match Interface.Impls.read_signature lookups.interface owner with
      | Some signature -> signature.generics <> [] || signature.capability_parameters <> []
      | None -> true)

let prove_defaults (frame : State.frame) owner =
  let lookups = frame.environment.lookups in
  let is_generic = is_generic_owner lookups owner in
  List.filter_map
    (fun (default : Mir.code Mir.default) ->
      let path = Path.Default { owner; variant = default.variant; name = default.name } in
      ignore
        (Lambdas.run_code frame default.value.tree
           ~type_:
             (Encoding.substitute_type frame
                (Interface.Definition.read_constant_type lookups.interface path)));
      if (not is_generic) && Cycles.is_evaluated_constant frame.environment path default.value.tree
      then Some path
      else None)
    (match Mir.read_defaults lookups.mir owner with
    | Some { form = defaults; _ } -> defaults
    | None -> [])

let translate_defaults (lookups : Lookups.t) (source : State.source) ~path =
  let start = start_proof lookups source ~current:path in
  Option.iter
    (fun ({ form = code; _ } : Mir.t Mir.sourced) ->
      Cycles.reject_constant_cycle start ~is_constant:false code)
    (Mir.read_code lookups.mir path);
  let evaluated_constants = prove_defaults start path in
  { (make_outcome start.query) with evaluated_constants }

let translate_type (lookups : Lookups.t) (source : State.source) ~path =
  let start = start_proof lookups source ~current:path in
  let evaluated_constants =
    match Mir.read_type_clauses lookups.mir path with
    | Some { form = { invariants; potential }; _ } ->
        let ty =
          match Interface.Definition.find_interface lookups.interface path with
          | Some (Interface.Environment.Type_interface interface) ->
              Types.Named { path; arguments = Types.list_generic_arguments interface.type_generics }
          | _ -> Facts.raise_bug "%s is not a type" (Path.show path)
        in
        let start = { start with self_type = Some ty } in
        let evaluated_constants = prove_defaults start path in
        (match Cycles.list_circular_clauses start ~type_:ty with
        | _ :: _ as circular -> List.iter (Cycles.reject_circular_proof start) circular
        | [] ->
            let value_ = Encoding.arrive start "value" ty in
            Facts.assume start
              (Validity.make_validity start ~assuming:true ~includes_invariants:false ty value_);
            let at_value = { start with self = Some value_; old_self = Some value_ } in
            List.iter
              (fun (invariant : Mir.requirement) ->
                let after, holds = Validity.read_specification at_value invariant.clause in
                Facts.assume after holds)
              invariants;
            Option.iter
              (fun (written : Mir.formula) ->
                let _, potential_term = Validity.read_specification at_value written in
                Obligations.oblige at_value
                  (Facts.locate at_value written.origin)
                  (Negative_potential { type_ = ty })
                  (Logic.less_equal (Logic.int 0) potential_term))
              potential);
        evaluated_constants
    | None -> []
  in
  { (make_outcome start.query) with evaluated_constants }

let translate_constant (lookups : Lookups.t) (source : State.source) ~path =
  let start = start_proof lookups source ~current:path in
  match Mir.read_initializer lookups.mir path with
  | Some { form = code; _ } ->
      let frame = start in
      Cycles.reject_constant_cycle frame ~is_constant:true code;
      ignore
        (Lambdas.run_code frame code
           ~type_:(Interface.Definition.read_constant_type start.environment.lookups.interface path));
      {
        (make_outcome start.query) with
        evaluated_constants =
          (if Cycles.is_evaluated_constant start.environment path code then [ path ] else []);
      }
  | None -> Facts.raise_bug "the constant `%s` has no MIR" (Path.show path)
