let make_context ?node ?(condition = []) ?(keeps_termination = true) ?(keeps_failures = true)
    ?(panics = false) ?(can_declare_panic = false) ?panic_condition (lookups : Lookups.t) ~home
    ~current ~terminates ~measures ~inherits_precondition =
  let node = Option.value node ~default:current in
  let rec context =
    {
      State.condition;
      bounds = Facts.list_definition_bounds lookups ~current ~condition;
      keeps_termination;
      keeps_failures;
      panics;
      can_declare_panic;
      panic_condition;
      obligation_condition = [];
      skipped_conditions = [];
      run_body = (fun frame ~lambdas body -> Reader.read_body context frame ~lambdas body);
      read_formula =
        (fun frame formula ~arguments -> Reader.read_formula context frame formula ~arguments);
      home;
      laws_assumed = [];
      lookups;
      current;
      node;
      terminates;
      measures;
      declarations = [];
      declared = Tables.Symbol_table.create 64;
      definitions = Tables.Symbol_table.create 8;
      datatypes = Tables.Type_table.create 16;
      visible_types = Tables.Type_table.create 16;
      type_clauses = Tables.Path_table.create 16;
      callees = Tables.Path_table.create 16;
      stated = Tables.Stated_table.create 64;
      facts = [];
      scopes = [];
      quantifier_facts = Tables.Term_table.create 16;
      written_quantifiers = Tables.Term_table.create 4;
      quantifier_symbols = [];
      obligations = [];
      fresh = 0;
      values = [];
      local_names = Tables.Local_table.create 16;
      local_origins = Tables.Local_table.create 16;
      returns = [];
      enclosing_provides = [];
      lent_back = [];
      instantiating = [];
      axiomatizing = [];
      open_axioms = [];
      axioms_of = Tables.Symbol_table.create 16;
      axiom_clauses = Tables.Axiom_clause_table.create 16;
      lending = None;
      callbacks = [];
      counters = [];
      conditional_counters = [];
      bounded_counters = [];
      recursive_costs_assumed = 0;
      fresh_order = Tables.Symbol_table.create 64;
      logs = [];
      powers = [];
      lambda_costs = [];
      lambda_captures = [];
      call_amounts = [];
      lambda_definitions = Tables.Symbol_table.create 8;
      potentials = [];
      models = Tables.Model_table.create 16;
      holds_potential = Tables.Type_table.create 16;
      buffers = Tables.Type_table.create 16;
      equalities = [];
      path_notes = [];
      entry = [];
      inherits_precondition;
      holes = [];
      unfinished = [];
      call_targets = [];
      reading_callback = false;
      validating = [];
      ranking = terminates && measures = [] && lookups.list_recursion_group node <> [];
      disjoint = lookups.list_must_be_disjoint home;
      indexes = [];
    }
  in
  context

let make_outcome (context : State.context) =
  {
    Obligation.obligations = List.rev context.obligations;
    holes = List.rev context.holes;
    evaluation = None;
  }

let make_empty_frame source =
  {
    State.source;
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
    yielded = None;
    yielded_so_far = None;
    spent = [];
  }

type promise = {
  counter : Costs.counter;
  clause : Mir.cost;
  written_in : State.source;
  inherited : bool;
}

let list_promises context (source : State.source) locals (costs : Mir.cost list) ~inherited =
  List.filter_map
    (fun (cost : Mir.cost) ->
      match Contracts.find_resource cost ~locals with
      | None -> Facts.raise_unsupported (Facts.locate context source cost.origin) Calls_target
      | Some resource ->
          let counter =
            {
              Costs.resource;
              counting = Lambdas.classify_counting cost;
              amortized = cost.amortized;
            }
          in
          (match (cost.resource, resource) with
          | Calls (Function_parameter local), Calls (Through term) ->
              context.call_targets <- (term, local) :: context.call_targets
          | _ -> ());
          if counter.counting = Units && not (List.mem counter context.bounded_counters) then
            context.bounded_counters <- counter :: context.bounded_counters;
          Some { counter; clause = cost; written_in = source; inherited })
    costs

let find_promiser (lookups : Lookups.t) (source : State.source) : Catalog.Prover.promiser =
  match source.key with
  | { path = Method { owner; _ }; _ }
    when Resolve.Names.find_kind lookups.interface.names owner = Some Resolve.Names.Capability ->
      Capability_promiser
  | _ -> Trait_promiser

let classify_counting (promise : promise) : Catalog.Prover.counting =
  match promise.counter.counting with Units | At_most -> Upper_bound | Exactly -> Exact

let keep_promise ?restated context (frame : State.frame) (promise : promise) ~(at : State.frame)
    ~location ~compute_change =
  let spent =
    match List.assoc_opt promise.counter frame.spent with Some term -> term | None -> Costs.zero
  in
  let spent = if promise.clause.amortized then Costs.plus spent (compute_change ()) else spent in
  let amount =
    match promise.clause.bound with
    | Order_of amount | At_most amount | Exactly amount ->
        snd (Validity.read_specification context { at with makes_obligations = false } amount)
  in
  let goal =
    match promise.counter.counting with
    | Units -> Logic.less_equal spent (Costs.bound amount)
    | Exactly -> Logic.equal spent amount
    | At_most -> Logic.less_equal spent amount
  in
  let counting = classify_counting promise
  and clause = Facts.quote promise.written_in promise.clause.origin in
  Facts.oblige context frame location ~holds_when:promise.clause.holds_when
    (Cost_promise
       (match restated with
       | Some (for_type, name, trait, declared) ->
           Restated_promise { counting; for_type; name; clause; trait; declared }
       | None when promise.inherited ->
           Inherited_promise
             { counting; promiser = find_promiser context.lookups promise.written_in; clause }
       | None -> Own_promise { counting; clause }))
    goal

let translate_run ~proof ?inherited ~substitution ~condition ~assumes_panic_condition
    (lookups : Lookups.t) (source : State.source) ~path =
  let contract =
    match Mir.read_contract lookups.mir path with
    | Some { form; _ } -> form
    | None -> Facts.raise_bug "`%s` has no MIR of its contract" source.name
  in
  let parameters = contract.parameters in
  let signature =
    Option.map
      (Types.map_signature (Types.substitute_erased substitution))
      (Interface.Impls.read_signature lookups.interface path)
  in
  let is_update_step =
    match signature with
    | Some (signature : Types.signature) -> signature.is_update_step
    | None -> false
  in
  let uses =
    match signature with
    | Some (signature : Types.signature) -> signature.uses
    | None -> Types.make_capability_set [ Built_in Run_forever ]
  in
  let implies = Conditions.implies lookups ~current:path in
  let terminates = proof || Types.terminates_when ~implies condition uses in
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
  let has_trait_frame =
    match inherited with
    | Some ((clauses : State.clauses), _) ->
        List.length clauses.parameters = List.length (pair_up parameters)
    | None -> false
  in
  let home = source.key in
  let measures =
    List.filter
      (fun (measure : Mir.formula) -> implies condition measure.holds_when)
      contract.decreases
  in
  let context =
    make_context lookups ~condition ~keeps_termination ~keeps_failures ~panics ~can_declare_panic
      ?panic_condition ~home ~current:path
      ~node:
        (Mir.Call_edges.resolve_node
           { interface = lookups.interface; mir = lookups.mir }
           path substitution)
      ~terminates ~measures ~inherits_precondition:has_trait_frame
  in
  List.iter
    (fun (measure : Mir.formula) ->
      ignore (Conditions.decide context ~substitution:Types.no_substitution measure.holds_when))
    contract.decreases;
  let keep_clauses ~substitution (clauses : State.clauses) =
    let decide holds_when =
      Conditions.find_obligation_condition (Conditions.decide context ~substitution holds_when)
    in
    {
      clauses with
      requires =
        List.filter_map
          (fun (requirement : Mir.requirement) ->
            Option.map
              (fun holds_when ->
                { requirement with clause = { requirement.clause with holds_when } })
              (decide requirement.clause.holds_when))
          clauses.requires;
      ensures =
        List.filter_map
          (fun (clause : Mir.formula) ->
            Option.map (fun holds_when -> { clause with holds_when }) (decide clause.holds_when))
          clauses.ensures;
      costs =
        List.filter_map
          (fun (cost : Mir.cost) ->
            Option.map (fun holds_when -> { cost with holds_when }) (decide cost.holds_when))
          clauses.costs;
    }
  in
  let contract =
    let kept =
      keep_clauses ~substitution:Types.no_substitution
        {
          callee = source;
          parameters = contract.parameters;
          panics_unless = contract.panics_unless;
          requires = contract.requires;
          ensures = contract.ensures;
          decreases = [];
          costs = contract.costs;
          callbacks = contract.callbacks;
          inherited = false;
          bindings = Types.no_substitution;
        }
    in
    { contract with requires = kept.requires; ensures = kept.ensures; costs = kept.costs }
  in
  let inherited =
    Option.map
      (fun ((clauses : State.clauses), substitution) ->
        (keep_clauses ~substitution clauses, substitution))
      inherited
  in
  context.callbacks <-
    List.filter_map
      (fun (position, callback) ->
        Option.map
          (fun (parameter : Mir.parameter) ->
            (parameter.local, Facts.read_parameter_name parameter, callback))
          (List.nth_opt parameters position))
      contract.callbacks;
  let declared_requires = Facts.list_clauses contract.requires
  and declared_ensures = contract.ensures in
  let output = match signature with Some { output = Returns ty; _ } -> Some ty | _ -> None in
  let declared_output =
    match Interface.Impls.read_signature lookups.interface path with
    | Some { output = Returns ty; _ } -> Some (Types.substitute substitution ty)
    | _ -> None
  in
  let start =
    List.fold_left
      (fun frame (parameter : Mir.parameter) ->
        match parameter.local with
        | Self ->
            let self_type = Facts.substitute_type context frame parameter.type_ in
            let self = Facts.arrive context frame "self" self_type in
            (match self with
            | Logic.Symbol symbol -> context.entry <- symbol :: context.entry
            | _ -> ());
            if not is_update_step then Validity.assume_valid context frame self_type self;
            { frame with self = Some self; self_type = Some self_type }
        | local ->
            let ty = Facts.substitute_type context frame parameter.type_ in
            let name = Facts.read_parameter_name parameter in
            let term = Facts.arrive context frame ("parameter." ^ name) ty in
            (match term with
            | Logic.Symbol symbol ->
                context.values <- (symbol, name) :: context.values;
                context.entry <- symbol :: context.entry
            | _ -> ());
            Validity.assume_valid context frame ty term;
            Facts.bind frame (Core_local local) ty term)
      { (make_empty_frame source) with substitution; is_ghost = proof }
      parameters
  in
  let start = { start with old_locals = start.locals; old_self = start.self } in
  let declared_output = Option.map (Facts.substitute_declared_type context start) declared_output in
  let output = Option.map (Facts.substitute_type context start) output in
  let start =
    match signature with
    | Some { output = Lends (_, part); _ } ->
        context.lending <-
          Some
            {
              part_type = part;
              part_postconditions = List.filter Amounts.mentions_result declared_ensures;
              return_postconditions =
                List.filter (fun clause -> not (Amounts.mentions_result clause)) declared_ensures;
            };
        { start with yielded_so_far = Some (Intrinsics.make_empty_parts context start part) }
    | _ -> start
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
  let find_trait_frame (at : State.frame) ~result =
    match inherited with
    | Some ((clauses : State.clauses), substitution) when has_trait_frame ->
        let locals, types, self, old_locals =
          List.fold_left2
            (fun (locals, types, self, old_locals) (parameter : Mir.parameter) (entry, exit_) ->
              match parameter.local with
              | Self -> (locals, types, Some (exit_, parameter.type_), old_locals)
              | local ->
                  ( Locals.add (Core_local local) exit_ locals,
                    Locals.add (Core_local local) parameter.type_ types,
                    self,
                    Locals.add (Core_local local) entry old_locals ))
            (Locals.empty, Locals.empty, None, Locals.empty)
            clauses.parameters
            (List.combine entry_terms (list_paired_values at))
        in
        Some
          ( clauses,
            {
              at with
              source = clauses.callee;
              locals;
              types;
              old_locals;
              self = Option.map fst self;
              old_self = start.self;
              self_type = Option.map (fun (_, ty) -> Types.substitute_erased substitution ty) self;
              result;
              makes_obligations = false;
              substitution;
            } )
    | _ -> None
  in
  let trait_requires =
    match find_trait_frame start ~result:None with
    | Some (clauses, inside) ->
        Logic.conjunction
          (List.map
             (fun requirement -> snd (Validity.read_specification context inside requirement))
             (Facts.list_clauses clauses.requires))
    | None -> Logic.Boolean true
  in
  let mir =
    match Mir.read_code lookups.mir path with
    | Some { form; _ } -> form
    | None -> Facts.raise_bug "`%s` has a body and no MIR" source.name
  in
  let promised =
    list_promises context source start.locals contract.costs ~inherited:false
    @
    match find_trait_frame start ~result:None with
    | Some (clauses, inside) ->
        list_promises context clauses.callee inside.locals clauses.costs ~inherited:true
    | None -> []
  in
  Lambdas.assign_counters context
    (List.map (fun promise -> (promise.counter, promise.clause.holds_when)) promised
    @ Lambdas.list_loop_counters context start.locals mir.body);
  let start =
    { start with spent = List.map (fun counter -> (counter, Costs.zero)) context.counters }
  in
  if context.inherits_precondition then
    if declared_requires = [] then Facts.assume context start trait_requires
    else
      ignore
        (List.fold_left
           (fun frame (requirement : Mir.formula) ->
             let frame, term =
               Conditions.with_obligation_condition context requirement.holds_when (fun () ->
                   Validity.read_specification context frame requirement)
             in
             Facts.oblige ~holds_when:requirement.holds_when context frame
               (Facts.locate context frame.source requirement.origin)
               (Impl_precondition { clause = Facts.quote source requirement.origin })
               term;
             frame)
           (Facts.restrict start trait_requires)
           declared_requires);
  (if context.inherits_precondition && contract.panics_unless <> [] then
     match find_trait_frame start ~result:None with
     | Some (clauses, inside) when clauses.panics_unless <> [] ->
         let trait_condition =
           Logic.conjunction
             (List.map
                (fun (requirement : Mir.requirement) ->
                  snd (Validity.read_specification context inside requirement.clause))
                clauses.panics_unless)
         in
         ignore
           (List.fold_left
              (fun frame (requirement : Mir.requirement) ->
                let frame, term = Validity.read_specification context frame requirement.clause in
                Facts.oblige context frame
                  (Facts.locate context frame.source requirement.clause.origin)
                  (Impl_panic_condition { clause = Facts.quote source requirement.clause.origin })
                  term;
                frame)
              (Facts.restrict (Facts.restrict start trait_requires) trait_condition)
              contract.panics_unless)
     | Some _ | None -> ());
  let start =
    List.fold_left
      (fun frame (requirement : Mir.formula) ->
        let frame, term =
          Conditions.with_obligation_condition context requirement.holds_when (fun () ->
              Validity.read_specification context frame requirement)
        in
        Facts.assume context frame term;
        frame)
      start declared_requires
  in
  let start =
    if assumes_panic_condition then
      List.fold_left
        (fun frame (requirement : Mir.requirement) ->
          let frame, term = Validity.read_specification context frame requirement.clause in
          Facts.assume context frame term;
          frame)
        start contract.panics_unless
    else start
  in
  List.iter
    (fun (promise : promise) ->
      if not promise.inherited then
        match promise.clause.bound with
        | Order_of amount | At_most amount | Exactly amount ->
            let result = Option.map (Facts.arrive context start "result") output in
            Conditions.with_obligation_condition context promise.clause.holds_when (fun () ->
                ignore (Validity.read_specification context { start with result } amount)))
    promised;
  Reader.read_body context start ~lambdas:mir.lambdas mir.body;
  let returns = List.rev context.returns in
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
  List.iter
    (fun ((frame : State.frame), returned) ->
      let frame = { frame with result = returned } in
      (match (returned, output) with
      | Some term, Some output ->
          Lambdas.check_valid context frame Whole_definition output term ~deep:true
            ~moment:Returned_value
      | _ -> ());
      List.iter
        (fun (parameter : Mir.parameter) ->
          match
            ( Locals.find_opt (Core_local parameter.local) frame.locals,
              Facts.find_local_type context frame (Core_local parameter.local) )
          with
          | Some term, Some ty ->
              Lambdas.check_valid context frame Whole_definition ty term ~deep:true
                ~moment:(Mut_parameter_at_return (Facts.read_parameter_name parameter))
          | _ -> ())
        mut_parameters;
      (match (mut_self, is_update_step, frame.self, frame.self_type) with
      | true, false, Some self, Some self_type ->
          Lambdas.check_valid context frame Whole_definition self_type self ~deep:true
            ~moment:Self_at_return
      | _ -> ());
      (match (context.lending, frame.yielded_so_far) with
      | Some { return_postconditions; _ }, Some yielded_so_far ->
          List.iter
            (fun (ensured : Mir.formula) ->
              let _, term =
                Validity.read_specification context
                  { frame with yielded = Some yielded_so_far }
                  ensured
              in
              Facts.oblige ~holds_when:ensured.holds_when context frame
                (Facts.locate context frame.source ensured.origin)
                (Ensures_at_method_end { clause = Facts.quote source ensured.origin })
                term)
            return_postconditions
      | _ ->
          List.iter
            (fun (ensured : Mir.formula) ->
              let _, term =
                Conditions.with_obligation_condition context ensured.holds_when (fun () ->
                    Validity.read_specification context frame ensured)
              in
              Facts.oblige ~holds_when:ensured.holds_when context frame
                (Facts.locate context frame.source ensured.origin)
                (Ensures_at_return { clause = Facts.quote source ensured.origin })
                term)
            declared_ensures);
      let compute_change () =
        let potential_change =
          List.fold_left
            (fun total (parameter : Mir.parameter) ->
              let entry, later, ty =
                match parameter.local with
                | Self -> (start.self, frame.self, frame.self_type)
                | local ->
                    ( Locals.find_opt (Core_local local) start.locals,
                      Locals.find_opt (Core_local local) frame.locals,
                      Facts.find_local_type context frame (Core_local local) )
              in
              match (parameter.mode, entry, ty) with
              | (Language.Mode.Mut | Language.Mode.Own), Some entry, Some ty ->
                  let potential_after =
                    match (parameter.mode, later) with
                    | Language.Mode.Mut, Some later ->
                        Amounts.compute_potential context frame ty later
                    | _ -> Costs.zero
                  in
                  Costs.plus total
                    (Costs.minus potential_after (Amounts.compute_potential context frame ty entry))
              | _ -> total)
            Costs.zero parameters
        in
        let potential_change =
          List.fold_left
            (fun total (ty, handed, back) ->
              Costs.minus total
                (Costs.minus
                   (Amounts.compute_potential context frame ty back)
                   (Amounts.compute_potential context frame ty handed)))
            potential_change context.lent_back
        in
        match (returned, declared_output) with
        | Some term, Some declared_output ->
            Costs.plus potential_change
              (Amounts.compute_potential context frame declared_output term)
        | _ -> potential_change
      in
      let under_trait = Facts.restrict frame trait_requires in
      List.iter
        (fun promise ->
          if promise.inherited then
            match find_trait_frame frame ~result:returned with
            | Some (_, inside) ->
                keep_promise context under_trait promise
                  ~at:{ inside with locals = inside.old_locals; self = inside.old_self }
                  ~location:Whole_definition ~compute_change
            | None -> ()
          else
            keep_promise context frame promise
              ~at:{ frame with locals = frame.old_locals; self = frame.old_self; result = returned }
              ~location:(Facts.locate context source promise.clause.origin)
              ~compute_change)
        promised;
      match find_trait_frame frame ~result:returned with
      | Some (clauses, inside) ->
          List.iter
            (fun (clause : Mir.formula) ->
              let _, term = Validity.read_specification context inside clause in
              Facts.oblige ~holds_when:clause.holds_when context under_trait Whole_definition
                (Promiser_ensures
                   {
                     promiser = find_promiser lookups clauses.callee;
                     clause = Facts.quote clauses.callee clause.origin;
                   })
                term)
            clauses.ensures
      | _ -> ())
    returns;
  (make_outcome context, context.skipped_conditions)

let translate_function ?(proof = false) ?inherited ?(substitution = Types.no_substitution)
    (lookups : Lookups.t) (source : State.source) ~path =
  let run ?(assumes_panic_condition = false) condition =
    translate_run ~proof ?inherited ~substitution ~condition ~assumes_panic_condition lookups source
      ~path
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
      ~inherits_precondition:false
  in
  let start = make_empty_frame source in
  let substitution = Contracts.make_trait_substitution lookups trait for_type in
  List.iter
    (fun (law_source, (law : Mir.law)) ->
      let types = Laws.list_law_parameter_types ~substitution law in
      if not (List.exists (fun ty -> Types.is_error ty) types) then begin
        context.laws_assumed <- (trait, for_type) :: context.laws_assumed;
        let terms =
          List.map
            (fun ty ->
              let term = Facts.arrive context start "law" ty in
              Validity.assume_valid context start ty term;
              term)
            types
        in
        let inside = Laws.bind_law_parameters start law_source ~substitution law terms in
        List.iter
          (fun clause ->
            Facts.assume context start (snd (Validity.read_specification context inside clause)))
          law.requires;
        let start =
          List.fold_left
            (fun (start : State.frame) ((proof_source : State.source), renaming) ->
              let proof =
                match Mir.find_code (lookups.mir.read_body_part proof_source.key) with
                | Some proof -> proof
                | None -> Facts.raise_bug "the proof `%s` has no MIR" proof_source.name
              in
              let parameters =
                List.map
                  (fun parameter ->
                    match proof.body.locals.(parameter) with
                    | { kind = Source { local; _ }; type_; _ } -> (local, type_)
                    | { kind = Temporary | Lent _; _ } ->
                        Facts.raise_bug "a parameter of the proof `%s` is a temporary"
                          proof_source.name)
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
        Facts.oblige context start at (Law_may_fail { trait; law = law.name; for_type }) holds
      end)
    (Laws.list_laws context trait.trait);
  make_outcome context

let prove_restated_method context (start : State.frame) ~at ~impl_interface ~trait ~for_type
    (restated : Types.restated_method) (clauses : State.clauses) =
  let lookups = context.State.lookups in
  let name = restated.restated_name and receiver = restated.restated_receiver in
  let restated_path = Path.Method { owner = trait.Types.trait; name; receiver } in
  let list_bounds =
    Interface.Properties.Bounds.close lookups.interface
      (Types.list_bounds impl_interface.Types.impl_generics)
  in
  let declared =
    match
      List.find_opt
        (fun (bound : Types.trait_reference) -> Path.equal bound.trait restated.declared_by)
        (Interface.Properties.list_bound_closure lookups.interface ~self:for_type trait)
    with
    | Some declared -> declared
    | None ->
        Facts.raise_bug "`%s` restates a method of `%s`, which it does not require"
          (Path.show trait.trait) (Path.show restated.declared_by)
  in
  match Interface.Impls.find_evidence lookups.interface ~list_bounds for_type declared with
  | Some (Evidence (Impl { impl; substitution })) -> (
      let evidence : Types.evidence = Impl { impl; substitution } in
      let signature =
        match Interface.Impls.read_signature lookups.interface restated_path with
        | Some signature -> signature
        | None ->
            Facts.raise_bug "the restated method `%s` has no signature" (Path.show restated_path)
      in
      let subtrait_substitution = Contracts.make_trait_substitution lookups trait for_type in
      let method_path = Path.Method { owner = impl; name; receiver } in
      let generic_arguments =
        List.map
          (fun (generic : Types.generic) -> Types.Type (Types.Parameter generic.generic))
          signature.generics
      in
      let callee_substitution =
        let generics =
          match Interface.Impls.read_signature lookups.interface method_path with
          | Some (implemented : Types.signature) ->
              List.map (fun (generic : Types.generic) -> generic.generic) implemented.generics
          | None -> []
        in
        let fixed =
          Types.combine_substitutions substitution
            (Contracts.make_trait_substitution lookups declared for_type)
        in
        let unbound =
          List.filter (fun generic -> Option.is_none (Types.find_argument generic fixed)) generics
        in
        if List.length unbound <> List.length generic_arguments then
          Facts.raise_bug "`%s` and the method `%s` that it restates take different generics"
            (Path.show restated_path) (Path.show method_path);
        List.fold_left2
          (fun substitution parameter argument ->
            Types.bind_argument parameter argument substitution)
          fixed unbound generic_arguments
      in
      match Contracts.find_method_contract context declared name receiver evidence with
      | None -> Facts.raise_bug "`%s` has no contract" (Path.show method_path)
      | Some contract ->
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
                  Facts.arrive context frame ("parameter." ^ Facts.read_parameter_name parameter) ty
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
            Validity.bind_arguments frame clauses ~arguments:(list_arguments frame)
              ~substitution:subtrait_substitution
          in
          let promised =
            list_promises context clauses.callee (reading entry).locals clauses.costs
              ~inherited:true
          in
          Lambdas.assign_counters context
            (List.map (fun promise -> (promise.counter, promise.clause.holds_when)) promised);
          let entry =
            { entry with spent = List.map (fun counter -> (counter, Costs.zero)) context.counters }
          in
          let result_type =
            Types.substitute_erased subtrait_substitution
              (Types.extract_result_type signature.output)
          in
          let invocation : Invocation.t =
            {
              callee =
                Trait_method
                  {
                    trait = declared;
                    name;
                    receiver;
                    self_type = for_type;
                    instantiation =
                      { type_arguments = generic_arguments; capability_arguments = [] };
                    evidence;
                  };
              lends =
                (match signature.output with Lends (mode, _) -> Some mode | Returns _ -> None);
              uses = Types.substitute_capabilities subtrait_substitution signature.uses;
            }
          in
          let after, result =
            Calls.call_contract context entry
              { origin = at; type_ = result_type }
              invocation method_path contract
              (List.mapi
                 (fun position (parameter : Mir.parameter) : State.passed ->
                   {
                     position;
                     mode = parameter.mode;
                     shape = Other;
                     origin = None;
                     passed_place =
                       (match parameter.mode with
                       | Language.Mode.Mut ->
                           Some
                             {
                               read = read_place parameter;
                               write = write_place parameter;
                               note_changed_in_place = (fun () -> ());
                             }
                       | Read | Own -> None);
                     type_ = Types.substitute_erased subtrait_substitution parameter.type_;
                     term = read_place parameter entry;
                   })
                 clauses.parameters)
              ~recursive_callee:None ~lent_final:None
              ~substitution_of:(fun _ -> callee_substitution)
              ~type_arguments:
                (Facts.list_method_type_arguments ~self_type:for_type generic_arguments)
          in
          let exit_ = reading after and entry_reading = reading entry in
          let ensuring =
            {
              exit_ with
              old_locals = entry_reading.locals;
              old_self = entry_reading.self;
              result = Some result;
            }
          in
          let location = Facts.locate context start.source at in
          List.iter
            (fun (clause : Mir.formula) ->
              let _, term = Validity.read_specification context ensuring clause in
              Facts.oblige context after location
                (Restated_contract
                   {
                     for_type;
                     name;
                     clause = Facts.quote clauses.callee clause.origin;
                     trait;
                     declared;
                   })
                term)
            clauses.ensures;
          List.iter
            (fun promise ->
              keep_promise context after promise ~at:entry_reading ~location
                ~compute_change:(fun () ->
                  List.fold_left
                    (fun total (parameter : Mir.parameter) ->
                      let ty = Types.substitute_erased subtrait_substitution parameter.type_ in
                      let before =
                        Amounts.compute_potential context after ty (read_place parameter entry)
                      in
                      match parameter.mode with
                      | Language.Mode.Mut ->
                          Costs.plus total
                            (Costs.minus
                               (Amounts.compute_potential context after ty
                                  (read_place parameter after))
                               before)
                      | Own -> Costs.minus total before
                      | Read -> total)
                    (Amounts.compute_potential context after result_type result)
                    clauses.parameters)
                ~restated:(for_type, name, trait, declared))
            promised)
  | Some Built_in ->
      Facts.raise_unsupported
        (Facts.locate context start.source at)
        (Compiler_restated_method { trait; declared_by = restated.declared_by })
  | Some (Evidence Bound) ->
      Facts.raise_bug "`%s` implements `%s` through a bound" (Types.show for_type)
        (Types.show_trait declared)
  | Some (Accepted _) | None -> ()

let translate_restated_clauses (lookups : Lookups.t) (source : State.source) ~impl ~trait ~for_type
    ~at =
  let home = source.key in
  let context =
    make_context lookups ~home ~current:impl ~terminates:false ~measures:[]
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
          prove_restated_method context (make_empty_frame source) ~at ~impl_interface ~trait
            ~for_type restated clauses
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
  | Some { form = { invariants; potential }; _ } ->
      let ty =
        match Interface.Definition.find_interface lookups.interface path with
        | Some (Interface.Environment.Type_interface interface) ->
            Types.Named { path; arguments = Types.list_generic_arguments interface.type_generics }
        | _ -> Facts.raise_bug "%s is not a type" (Path.show path)
      in
      let start = { (make_empty_frame source) with self_type = Some ty } in
      (match Mir.read_defaults lookups.mir path with
      | Some { form = Field_defaults defaults; _ } ->
          List.iter
            (fun (default : Mir.t Mir.field_default) ->
              ignore
                (Amounts.run_code context start default.value
                   ~type_:(Facts.substitute_type context start default.type_)))
            defaults
      | Some { form = Parameter_defaults _; _ } | None -> ());
      let value_ = Facts.arrive context start "value" ty in
      Facts.assume context start
        (Validity.make_validity context start ~assuming:true ~includes_invariants:false ty value_);
      let at_value = { start with self = Some value_; old_self = Some value_ } in
      List.iter
        (fun (invariant : Mir.requirement) ->
          let after, holds = Validity.read_specification context at_value invariant.clause in
          Facts.assume context after holds)
        invariants;
      Option.iter
        (fun (written : Mir.formula) ->
          let _, potential_term = Validity.read_specification context at_value written in
          Facts.oblige context at_value
            (Facts.locate context at_value.source written.origin)
            (Negative_potential { type_ = ty })
            (Logic.less_equal (Logic.int 0) potential_term))
        potential
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
      let frame = make_empty_frame source in
      Facts.reject_constant_cycle context frame code;
      ignore
        (Amounts.run_code context frame code
           ~type_:(Interface.Definition.read_constant_type context.lookups.interface path));
      {
        (make_outcome context) with
        evaluation =
          (if Facts.is_evaluated_constant context path code then Some (Constant_value path)
           else None);
      }
  | None -> Facts.raise_bug "the constant `%s` has no MIR" (Path.show path)

let translate_theorem lookups source ~path = translate_function ~proof:true lookups source ~path
