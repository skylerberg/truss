let lookup_argument_at_index (values : State.passed list) index =
  match
    List.find_map
      (fun (passed : State.passed) -> if passed.position = index then Some passed.term else None)
      values
  with
  | Some term -> term
  | None -> Logic.Boolean false

let list_type_names substitution =
  let shown =
    List.map
      (fun ((parameter : Types.parameter), ty) -> (parameter.name, Types.show ty))
      (Types.list_type_arguments substitution)
    |> List.sort_uniq compare
  in
  List.filter
    (fun (name, _) -> List.length (List.filter (fun (other, _) -> other = name) shown) = 1)
    shown

let list_required_fixes (context : State.context) (frame : State.frame) (clauses : State.clauses)
    (requirement : Mir.requirement) term (values : State.passed list) ~type_names =
  let clause = requirement.clause in
  let is_fixed name =
    List.mem name context.entry
    ||
    match name with
    | Logic.Symbol.Constant _ | Evaluated (Constant_value _) | Literal _ -> true
    | _ -> false
  in
  let is_simple text =
    String.for_all
      (fun character ->
        character = '_' || character = '.'
        || Char.code character >= 128
        || (character >= 'a' && character <= 'z')
        || (character >= 'A' && character <= 'Z')
        || (character >= '0' && character <= '9'))
      text
  in
  let list_written () =
    List.filter_map
      (fun (index, (parameter : Mir.parameter)) ->
        Option.bind
          (List.find_opt (fun (passed : State.passed) -> passed.position = index) values)
          (fun (passed : State.passed) ->
            Option.map
              (fun text -> (parameter.local, if is_simple text then text else "(" ^ text ^ ")"))
              (Facts.show_truss_value context passed.term)))
      (List.mapi (fun index parameter -> (index, parameter)) clauses.parameters)
  in
  if
    Facts.is_home context frame.source
    && List.for_all is_fixed (Logic.list_free_constants term)
    && List.exists (fun name -> List.mem name context.entry) (Logic.list_free_constants term)
    && not (Logic.is_refuted term)
  then begin
    let written = list_written () in
    let replacements =
      List.map
        (fun (local, origin) ->
          Option.map (fun text -> (origin, text)) (List.assoc_opt local written))
        requirement.names
    in
    if List.for_all Option.is_some replacements then
      Facts.add_requires context frame
        [
          Substituted_clause
            {
              clause = { key = clauses.callee.key; origin = clause.origin };
              replacements = List.filter_map Fun.id replacements;
              type_names;
            };
        ]
    else []
  end
  else []

let name_term context ty term =
  let rec holds_call = function
    | Logic.Apply ((Logic.Symbol.Function _ | Logic.Symbol.Limited _), _) -> true
    | Logic.Forall (_, _, body) | Logic.Exists (_, body) -> holds_call body
    | term -> List.exists holds_call (Logic.list_arguments term)
  in
  if not (holds_call term) then term
  else
    let symbol = Logic.Symbol.Named_term term in
    let named = Logic.Symbol symbol in
    Facts.run_once context (Value_of symbol) (fun () ->
        Facts.declare context (Logic.Constant (symbol, Facts.declare_sort context ty));
        Facts.add_fact context (Logic.equal named term));
    named

let is_datatype ty = match ty with Types.Named _ -> Types.find_builtin ty = None | _ -> false

let calls_update_step (context : State.context) (invocation : Invocation.t) =
  match invocation.callee with
  | Function { path; _ } -> (
      match Contracts.read_signature context path with
      | Some signature -> signature.is_update_step
      | None -> false)
  | Trait_method _ | Capability_method _ | Intrinsic _ | Indirect _ -> false

let havoc_mut context (frame : State.frame) (values : State.passed list) ~is_update_step
    ~list_modified =
  List.fold_left
    (fun (frame : State.frame) (passed : State.passed) ->
      match (passed.mode, passed.passed_place) with
      | Language.Mode.Mut, Some place ->
          if is_update_step && passed.position = 0 then place.note_changed_in_place ();
          let arrive ty = Facts.arrive context frame "changed" ty in
          let changed =
            Option.bind (list_modified passed.position) (fun parts ->
                List.fold_left
                  (fun whole (part : Types.modified) ->
                    Option.bind whole (fun whole ->
                        Validity.replace_part context passed.type_ whole part.field_path
                          (fun part_type before ->
                            if part.is_elements then
                              Intrinsics.replace_elements context frame part_type before
                            else arrive part_type)))
                  (Some passed.term) parts)
          in
          place.write frame (match changed with Some term -> term | None -> arrive passed.type_)
      | _ -> frame)
    frame values

let list_structural_parameters context (frame : State.frame) (clauses : State.clauses) =
  List.concat
    (List.mapi
       (fun index (parameter : Mir.parameter) ->
         match parameter.local with
         | Self -> (
             match (frame.old_self, frame.self_type) with
             | Some entry, Some ty when is_datatype ty -> [ (parameter, ty, entry, index) ]
             | _ -> [])
         | local -> (
             match
               ( Locals.find_opt (Core_local local) frame.old_locals,
                 Facts.find_local_type context frame (Core_local local) )
             with
             | Some entry, Some ty when is_datatype ty -> [ (parameter, ty, entry, index) ]
             | _ -> []))
       clauses.parameters)

let rec has_application_of symbol (term : Logic.term) =
  match term with
  | Apply (applied, _) when applied = symbol -> true
  | Forall (_, _, body) | Exists (_, body) -> has_application_of symbol body
  | _ -> List.exists (has_application_of symbol) (Logic.list_arguments term)

let find_definition ~symbol result (term : Logic.term) =
  match term with
  | Operation (Equal, [ left; right ]) when left = result && not (has_application_of symbol right)
    ->
      Some right
  | Operation (Equal, [ left; right ]) when right = result && not (has_application_of symbol left)
    ->
      Some left
  | _ -> None

let add_restated_clauses (context : State.context) ~self_type ~bind trait name receiver
    (contract : State.contract) =
  {
    contract with
    restated_clauses =
      List.map
        (fun ((subtrait : Types.trait_reference), (clauses : State.clauses)) ->
          {
            clauses with
            bindings = bind subtrait (Path.Method { owner = subtrait.trait; name; receiver });
          })
        (Contracts.list_restated_clauses context
           ~packages:(Operations.list_impl_packages context self_type)
           ~self_type trait name receiver);
  }

let call_contract context (frame : State.frame) (site : Invocation.site) (invocation : Invocation.t)
    path (contract : State.contract) (values : State.passed list) ~recursive_callee ~lent_final
    ~substitution_of ~type_arguments =
  let substitution_of (clauses : State.clauses) =
    Types.combine_substitutions (substitution_of clauses) clauses.bindings
  in
  let find_clause_condition (clauses : State.clauses) holds_when =
    Conditions.find_obligation_condition
      (Conditions.decide context ~substitution:(substitution_of clauses) holds_when)
  in
  let keep_holding_clauses (clauses : State.clauses) =
    let holds holds_when = Option.is_some (find_clause_condition clauses holds_when) in
    {
      clauses with
      requires =
        List.filter
          (fun (requirement : Mir.requirement) -> holds requirement.clause.holds_when)
          clauses.requires;
      ensures = List.filter (fun (clause : Mir.formula) -> holds clause.holds_when) clauses.ensures;
      decreases =
        List.filter (fun (measure : Mir.formula) -> holds measure.holds_when) clauses.decreases;
      costs = List.filter (fun (cost : Mir.cost) -> holds cost.holds_when) clauses.costs;
    }
  in
  let contract =
    {
      contract with
      callee_clauses = keep_holding_clauses contract.callee_clauses;
      trait_clauses = Option.map keep_holding_clauses contract.trait_clauses;
      restated_clauses = List.map keep_holding_clauses contract.restated_clauses;
    }
  in
  let is_logic_call =
    contract.is_logic_function
    && Facts.remove_panic_condition invocation.uses = Types.no_capabilities
  in
  let values =
    if is_logic_call then
      List.map
        (fun (passed : State.passed) ->
          if passed.mode = Language.Mode.Mut || Logic.mentions frame.bound passed.term then passed
          else { passed with term = name_term context passed.type_ passed.term })
        values
    else values
  in
  let caller = frame.source in
  let location = Facts.locate context frame.source site.origin in
  let find_argument_at index =
    List.find_map
      (fun (passed : State.passed) -> if passed.position = index then Some passed.term else None)
      values
  in
  let list_bindings (clauses : State.clauses) =
    List.mapi
      (fun index (parameter : Mir.parameter) -> (parameter, find_argument_at index))
      clauses.parameters
  in
  let bind bindings =
    List.fold_left
      (fun (locals, types, self) ((parameter : Mir.parameter), term) ->
        match (parameter.local, term) with
        | Self, Some term -> (locals, types, Some (term, parameter.type_))
        | local, Some term ->
            ( Locals.add (Core_local local) term locals,
              Locals.add (Core_local local) parameter.type_ types,
              self )
        | _, None -> (locals, types, self))
      (Locals.empty, Locals.empty, None)
      bindings
  in
  let self_of self = Option.map fst self
  and find_self_type clauses self =
    Option.map (fun (_, ty) -> Types.substitute_erased (substitution_of clauses) ty) self
  in
  let read_entry_frame (clauses : State.clauses) =
    let locals, types, self = bind (list_bindings clauses) in
    {
      frame with
      source = clauses.callee;
      locals;
      types;
      old_locals = locals;
      self = self_of self;
      old_self = self_of self;
      self_type = find_self_type clauses self;
      result = None;
      makes_obligations = false;
      substitution = substitution_of clauses;
    }
  in
  let callee_clauses = contract.callee_clauses in
  let is_self_call = Option.equal Path.equal recursive_callee (Some context.node) in
  if Option.is_some recursive_callee then
    begin match (context.measures, callee_clauses.decreases) with
    | [], []
      when context.terminates && is_self_call
           && list_structural_parameters context frame callee_clauses <> [] ->
        let pairs = list_structural_parameters context frame callee_clauses in
        let before = List.map (fun (_, ty, entry, _) -> Models.rank context ty entry) pairs in
        let after =
          List.map
            (fun (_, ty, _, index) ->
              Models.rank context ty (lookup_argument_at_index values index))
            pairs
        in
        let compared =
          List.map (fun (parameter, _, _, _) -> Facts.read_parameter_name parameter) pairs
        in
        Facts.oblige context frame location
          (Recursion_not_on_part { call = { at = location; callee = Some path }; compared })
          (Amounts.compare_lexicographically before after)
    | ([], _ | _, []) when context.terminates ->
        Facts.oblige context frame location
          (Recursion_may_not_end { call = { at = location; callee = Some path }; is_self_call })
          (Logic.Boolean false)
    | (_ :: _ as measures), (_ :: _ as callee_measures) ->
        let current_frame =
          { frame with makes_obligations = false; locals = frame.old_locals; self = frame.old_self }
        in
        let callee_entry = read_entry_frame callee_clauses in
        let rec split_prefix before after =
          match (before, after) with
          | right_term :: before, left_term :: after ->
              let rest_before, rest_after = split_prefix before after in
              (right_term :: rest_before, left_term :: rest_after)
          | _ -> ([], [])
        in
        let before =
          List.map
            (fun measure -> snd (Validity.read_specification context current_frame measure))
            measures
        in
        let after =
          List.map
            (fun measure -> snd (Validity.read_specification context callee_entry measure))
            callee_measures
        in
        let before, after = split_prefix before after in
        Facts.oblige context frame location
          (Measure_may_not_decrease
             {
               call = { at = location; callee = None };
               measures =
                 List.map
                   (fun (measure : Mir.formula) -> Facts.quote caller measure.origin)
                   measures;
             })
          (Amounts.compare_lexicographically before after)
    | [], _ | _, [] -> ()
    end;
  let precondition_clauses = Contracts.select_precondition_clauses contract in
  let read_required () =
    let entry = read_entry_frame precondition_clauses in
    List.map
      (fun (requirement : Mir.requirement) ->
        let clause = requirement.clause in
        let _, term = Validity.read_specification context entry clause in
        let cited = Some (precondition_clauses.callee.key, clause.origin) in
        let fixes =
          list_required_fixes context frame precondition_clauses requirement term values
            ~type_names:(list_type_names (substitution_of precondition_clauses))
        in
        Facts.oblige ?cited ~fixes
          ?holds_when:(find_clause_condition precondition_clauses clause.holds_when)
          context frame location
          (Precondition_may_fail
             {
               clause = Facts.quote precondition_clauses.callee clause.origin;
               call = { at = location; callee = Some path };
             })
          term;
        term)
      precondition_clauses.requires
  in
  let required =
    if List.exists (Path.equal path) context.reading_requires then Logic.Boolean true
    else begin
      let reading_requires = context.reading_requires in
      context.reading_requires <- path :: reading_requires;
      Fun.protect
        ~finally:(fun () -> context.reading_requires <- reading_requires)
        (fun () -> Logic.conjunction (read_required ()))
    end
  in
  if not (context.panics || Types.has_capability (Built_in Panic) invocation.uses) then begin
    let clauses = contract.callee_clauses in
    let entry = read_entry_frame clauses in
    List.iter
      (fun (requirement : Mir.requirement) ->
        let _, term = Validity.read_specification context entry requirement.clause in
        let fixes =
          list_required_fixes context frame clauses requirement term values
            ~type_names:(list_type_names (substitution_of clauses))
        in
        let cited = Some (clauses.callee.key, requirement.clause.origin) in
        Facts.oblige ?cited ~fixes context frame location
          (Precondition_may_panic
             {
               clause = Facts.quote clauses.callee requirement.clause.origin;
               call = { at = location; callee = Some path };
             })
          term)
      clauses.panics_unless
  end;
  let compute_required (clauses : State.clauses) =
    if clauses == precondition_clauses then required
    else
      Logic.conjunction
        (List.map
           (fun requirement ->
             snd (Validity.read_specification context (read_entry_frame clauses) requirement))
           (Facts.list_clauses clauses.requires))
  in
  let after =
    havoc_mut context frame values
      ~is_update_step:(calls_update_step context invocation)
      ~list_modified:(Contracts.list_modified_parts context path)
  in
  let in_quantifier = is_logic_call && frame.binders <> [] in
  let state term =
    if in_quantifier then Facts.add_frame_fact context after term
    else Facts.assume context after term
  in
  let changed =
    List.filter_map
      (fun (passed : State.passed) ->
        match (passed.mode, passed.passed_place) with
        | Language.Mode.Mut, Some place ->
            Some
              (passed.position, Facts.read_or_arrive context after "changed" passed.type_ place.read)
        | _ -> None)
      values
  in
  let callee_bindings = list_bindings callee_clauses in
  let callee_arguments = List.filter_map snd callee_bindings in
  let is_on_bound_values = List.exists (Logic.mentions after.bound) callee_arguments in
  let declared_result_type = Facts.substitute_declared_type context frame site.type_ in
  let result_type = Types.erase_views declared_result_type in
  let applied_as = ref None in
  let definition = ref None in
  let is_limited_call = ref false in
  let result =
    if is_logic_call && List.length callee_arguments = List.length callee_bindings then begin
      let function_symbol = Logic.Symbol.Function { callee = path; type_arguments } in
      let sorts =
        List.mapi
          (fun index ((parameter : Mir.parameter), _) ->
            match List.find_opt (fun (passed : State.passed) -> passed.position = index) values with
            | Some passed -> Facts.declare_sort context passed.type_
            | None ->
                Facts.declare_sort context
                  (Types.erase_views
                     ((Interface.Impls.normalize context.lookups.interface
                         ~list_bounds:context.bounds)
                        (Types.substitute (substitution_of callee_clauses) parameter.type_))))
          callee_bindings
      in
      let result_sort = Facts.declare_sort context result_type in
      Facts.declare context (Logic.Function (function_symbol, sorts, result_sort));
      (match (path, callee_bindings) with
      | Method { owner = Impl { trait; _ } as impl; name; receiver }, [ (self, _) ]
        when self.local = Self
             && Well_known.is_method Model_model (Method { owner = trait.path; name; receiver }) ->
          Models.rank_model context
            (Types.erase_views
               ((Interface.Impls.normalize context.lookups.interface ~list_bounds:context.bounds)
                  (Types.substitute (substitution_of callee_clauses) self.type_)))
            ~model:result_type ~impl function_symbol
      | _ -> ());
      let symbol =
        if List.mem function_symbol context.axiomatizing then begin
          is_limited_call := true;
          let limited = Logic.Symbol.Limited { callee = path; type_arguments } in
          Facts.declare context (Logic.Function (limited, sorts, result_sort));
          Facts.run_once context (Limited_link function_symbol) (fun () ->
              let parameters =
                List.mapi
                  (fun index sort ->
                    (Logic.Symbol.Variable { label = "linked"; numbers = [ index ] }, sort))
                  sorts
              in
              let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
              let applied = Logic.Apply (function_symbol, inputs) in
              Facts.add_fact context
                (Logic.forall ~trigger:[ applied ]
                   (parameters, Logic.equal applied (Logic.Apply (limited, inputs)))));
          limited
        end
        else function_symbol
      in
      applied_as := Some (symbol, sorts);
      let term = Logic.Apply (symbol, callee_arguments) in
      Facts.assume context after (Facts.make_in_range result_type term);
      if Facts.find_bounds result_type <> None && is_on_bound_values then
        Facts.run_once context (In_range symbol) (fun () ->
            let parameters =
              List.mapi
                (fun index sort ->
                  (Logic.Symbol.Variable { label = "ranged"; numbers = [ index ] }, sort))
                sorts
            in
            Facts.add_fact context
              (Logic.forall
                 ( parameters,
                   Facts.make_in_range result_type
                     (Logic.Apply (symbol, List.map (fun (name, _) -> Logic.Symbol name) parameters))
                 )));
      term
    end
    else Facts.arrive context after "result" result_type
  in
  Validity.assume_valid context after result_type result;
  let left_valid =
    match (contract.result_kind, invocation.lends, lent_final) with
    | `Lends, Some Language.Mode.Mut, Some leave ->
        Some
          ( Validity.make_validity context after ~assuming:false ~deep:true result_type
              (leave result),
            leave )
    | _ -> None
  in
  let check_left () =
    match left_valid with
    | Some (_, leave) ->
        Lambdas.check_valid context after location result_type (leave result) ~deep:true
          ~moment:When_lend_ends
    | None -> ()
  in
  let is_update_step = calls_update_step context invocation in
  List.iter
    (fun (passed : State.passed) ->
      if passed.mode = Language.Mode.Mut && not (is_update_step && passed.position = 0) then
        match List.assoc_opt passed.position changed with
        | Some term ->
            let valid = Validity.make_validity context after ~assuming:true passed.type_ term in
            Facts.assume context after
              (match left_valid with Some (left, _) -> Logic.( ==> ) left valid | None -> valid)
        | None -> ())
    values;
  if not (List.exists (Path.equal path) context.instantiating) then begin
    context.instantiating <- path :: context.instantiating;
    let axiom_symbol =
      match !applied_as with
      | Some (symbol, sorts)
        when contract.result_kind = `Returns && (not !is_limited_call)
             && not (Types.equal result_type Types.unit) ->
          Some (symbol, sorts)
      | _ -> None
    in
    let make_parameters label sorts =
      context.fresh <- context.fresh + 1;
      let axiom = context.fresh in
      List.mapi
        (fun index sort -> (Logic.Symbol.Variable { label; numbers = [ axiom; index ] }, sort))
        sorts
    in
    let find_readable_clause mark clause inside =
      match snd (Validity.read_specification context inside clause) with
      | term when not (Facts.mentions_fresh_after context mark term) -> Some term
      | _ -> None
      | exception Facts.Unsupported _ -> None
    in
    let make_parameters_valid outside inputs =
      Logic.conjunction
        (List.map2
           (fun ((parameter : Mir.parameter), _) input ->
             let ty = Types.substitute_erased (substitution_of callee_clauses) parameter.type_ in
             Logic.( &&& ) (Facts.make_in_range ty input)
               (Validity.make_validity context outside ~assuming:true ty input))
           callee_bindings inputs)
    in
    let axiomatize symbol parameters make =
      let mark = context.fresh in
      let facts = ref [] in
      let axiom = { State.parameters = List.map fst parameters; hypotheses = []; at_calls = [] } in
      let scopes = context.scopes and open_axioms = context.open_axioms in
      context.axiomatizing <- symbol :: context.axiomatizing;
      context.scopes <- List.map (fun (name, _) -> (name, facts)) parameters @ scopes;
      context.open_axioms <- axiom :: open_axioms;
      Fun.protect
        ~finally:(fun () ->
          context.axiomatizing <- List.tl context.axiomatizing;
          context.scopes <- scopes;
          context.open_axioms <- open_axioms)
        (fun () ->
          let stated = make () in
          let drop_fresh_terms terms =
            List.filter
              (fun term -> not (Facts.mentions_fresh_after context mark term))
              (List.rev terms)
          in
          axiom.hypotheses <- drop_fresh_terms axiom.hypotheses;
          (stated, Logic.conjunction (drop_fresh_terms !facts), axiom))
    in
    let record_axiom symbol axiom = Tables.Symbol_table.add context.axioms_of symbol axiom in
    let add_contract_axiom ~is_triggered symbol sorts =
      Facts.run_once context (Contract_of symbol) (fun () ->
          let parameters = make_parameters "ensured" sorts in
          let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
          let arguments = List.mapi (fun index input -> (index, input)) inputs in
          let applied = Logic.Apply (symbol, inputs) in
          let outside =
            {
              after with
              bound = List.map fst parameters;
              binders = [];
              condition = Logic.Boolean true;
              makes_obligations = false;
            }
          in
          let mark = context.fresh in
          let stated, facts, axiom =
            axiomatize symbol parameters (fun () ->
                let valid = make_parameters_valid outside inputs in
                let readable_clauses =
                  List.filter_map
                    (fun (clauses : State.clauses) ->
                      let inside =
                        {
                          (Validity.bind_arguments outside clauses ~arguments
                             ~substitution:(substitution_of clauses))
                          with
                          result = Some applied;
                          makes_obligations = false;
                        }
                      in
                      let required =
                        List.map
                          (fun requirement -> find_readable_clause mark requirement inside)
                          (Facts.list_clauses clauses.requires)
                      in
                      if List.mem None required then None
                      else
                        match
                          List.filter_map
                            (fun (clause : Mir.formula) ->
                              Option.map
                                (fun term -> (clause, term))
                                (find_readable_clause mark clause inside))
                            clauses.ensures
                        with
                        | [] -> None
                        | ensures -> Some (clauses, List.filter_map Fun.id required, ensures))
                    (Contracts.list_declared_clauses contract)
                in
                if readable_clauses = [] || Facts.mentions_fresh_after context mark valid then None
                else Some (valid, readable_clauses))
          in
          match stated with
          | None -> ()
          | Some (valid, readable_clauses) -> (
              let has_quantifier_through_definitions body =
                Logic.has_quantifier body
                || Logic.mentions
                     (List.of_seq (Tables.Symbol_table.to_seq_keys context.definitions))
                     body
              in
              let definition =
                match (is_triggered, facts, readable_clauses) with
                | ( true,
                    Logic.Boolean true,
                    [ (_, required, [ (_, Logic.Operation (Equal, [ left; right ])) ]) ] ) -> (
                    let defined_by body =
                      if
                        Logic.mentions [ symbol ] body
                        || Facts.find_bounds result_type <> None
                        || not (has_quantifier_through_definitions body)
                      then None
                      else Some (required, body)
                    in
                    match (left, right) with
                    | _ when left = applied -> defined_by right
                    | _ when right = applied -> defined_by left
                    | _ -> None)
                | _ -> None
              in
              if is_triggered then
                List.iter
                  (fun ((clauses : State.clauses), _, ensures) ->
                    List.iter
                      (fun ((clause : Mir.formula), _) ->
                        Tables.Axiom_clause_table.replace context.axiom_clauses
                          (symbol, clauses.callee.name, clause.origin)
                          ())
                      ensures)
                  readable_clauses;
              record_axiom symbol axiom;
              match definition with
              | Some (required, body) ->
                  let unspecified = Logic.Symbol.Unspecified symbol
                  and result_sort = Facts.declare_sort context result_type in
                  Facts.declare context (Logic.Function (unspecified, sorts, result_sort));
                  Facts.declare context
                    (Logic.Definition
                       {
                         symbol;
                         parameters;
                         result = result_sort;
                         body =
                           Logic.ite
                             (Logic.conjunction ((valid :: axiom.hypotheses) @ required))
                             body
                             (Logic.Apply (unspecified, inputs));
                       })
              | None ->
                  Facts.add_fact context
                    (Logic.forall
                       ~trigger:(if is_triggered then [ applied ] else [])
                       ( parameters,
                         Logic.( ==> )
                           (Logic.conjunction (valid :: axiom.hypotheses))
                           (Logic.conjunction
                              (facts
                              :: List.map
                                   (fun (_, required, ensures) ->
                                     Logic.( ==> ) (Logic.conjunction required)
                                       (Logic.conjunction (List.map snd ensures)))
                                   readable_clauses)) ))))
    in
    (match (!is_limited_call, axiom_symbol, !applied_as) with
    | true, _, _ -> ()
    | false, Some (symbol, sorts), _ -> add_contract_axiom ~is_triggered:true symbol sorts
    | false, None, Some (symbol, sorts) when is_on_bound_values ->
        add_contract_axiom ~is_triggered:false symbol sorts
    | false, None, _ -> ());
    let is_in_axiom (clauses : State.clauses) (clause : Mir.formula) =
      match axiom_symbol with
      | Some (symbol, _) ->
          Tables.Axiom_clause_table.mem context.axiom_clauses
            (symbol, clauses.callee.name, clause.origin)
      | None -> false
    in
    let assume_ensures is_kept =
      List.iter
        (fun (clauses : State.clauses) ->
          let entry = list_bindings clauses in
          let exit_bindings =
            List.mapi
              (fun index (parameter, term) ->
                ( parameter,
                  match List.assoc_opt index changed with Some term -> Some term | None -> term ))
              entry
          in
          let entry_locals, types, entry_self = bind entry in
          let exit_locals, _, exit_self = bind exit_bindings in
          let is_unbound_in_quantifier = in_quantifier && not is_on_bound_values in
          let ensures_frame =
            {
              frame with
              source = clauses.callee;
              condition = (if is_unbound_in_quantifier then Logic.Boolean true else after.condition);
              bound = (if is_unbound_in_quantifier then [] else frame.bound);
              binders = (if is_unbound_in_quantifier then [] else frame.binders);
              locals = exit_locals;
              types;
              old_locals = entry_locals;
              self = self_of exit_self;
              old_self = self_of entry_self;
              self_type = find_self_type clauses entry_self;
              result = Some result;
              makes_obligations = false;
              substitution = substitution_of clauses;
            }
          in
          let ensures_frame =
            match contract.result_kind with
            | `Lends when List.exists Amounts.mentions_history clauses.ensures ->
                let left = match lent_final with Some leave -> leave result | None -> result in
                let none = Intrinsics.make_empty_parts context after result_type in
                {
                  ensures_frame with
                  yielded = Some (Intrinsics.append_part context after result_type none left);
                }
            | `Lends | `Returns -> ensures_frame
          in
          List.iter
            (fun (clause : Mir.formula) ->
              if is_kept clause && not (!is_limited_call || is_in_axiom clauses clause) then
                let frame_for_clause =
                  if contract.result_kind = `Lends && Amounts.mentions_result clause then
                    {
                      ensures_frame with
                      locals = entry_locals;
                      self = self_of entry_self;
                      yielded = None;
                    }
                  else ensures_frame
                in
                match Validity.read_specification context frame_for_clause clause with
                | _, term ->
                    (match (!applied_as, !definition) with
                    | Some (symbol, _), None -> definition := find_definition ~symbol result term
                    | _ -> ());
                    state (Logic.( ==> ) (compute_required clauses) term)
                | exception Facts.Unsupported _ -> ())
            clauses.ensures)
        (Contracts.list_declared_clauses contract)
    in
    let is_about_part clause = contract.result_kind <> `Lends || Amounts.mentions_result clause in
    assume_ensures is_about_part;
    check_left ();
    assume_ensures (fun clause -> not (is_about_part clause));
    context.instantiating <- List.tl context.instantiating
  end
  else check_left ();
  (match !applied_as with
  | Some (symbol, _) when not !is_limited_call ->
      List.iter
        (fun (axiom : State.open_axiom) ->
          let substitute = Logic.substitute (List.combine axiom.parameters callee_arguments) in
          List.iter
            (fun hypothesis -> Amounts.assume_typed context after (substitute hypothesis))
            axiom.hypotheses;
          List.iter (fun apply_hook -> apply_hook after substitute) axiom.at_calls)
        (Tables.Symbol_table.find_all context.axioms_of symbol)
  | _ -> ());
  let compute_change () =
    Costs.plus
      (Amounts.compute_arguments_potential_change context ~before:frame ~after values ~changed)
      (match contract.result_kind with
      | `Lends -> (
          match lent_final with
          | Some leave ->
              Costs.minus
                (Amounts.compute_potential context after declared_result_type result)
                (Amounts.compute_potential context after declared_result_type (leave result))
          | None -> Costs.zero)
      | `Returns -> Amounts.compute_potential context after declared_result_type result)
  in
  let declared_clauses = Contracts.list_declared_clauses contract in
  let method_cost =
    lazy
      (if Laws.has_method_cost context invocation.callee path then
         Some (fun metric -> Amounts.compute_method_cost context frame metric invocation.callee)
       else None)
  in
  let list_metric_costs metric =
    List.concat_map
      (fun (clauses : State.clauses) ->
        List.filter (fun (cost : Mir.cost) -> cost.resource = Metric metric) clauses.costs)
      declared_clauses
  in
  let counts_provider_potential =
    match invocation.callee with
    | Capability_method _ -> true
    | Function _ | Trait_method _ | Indirect () | Intrinsic _ -> false
  in
  let note_amount (counter : Costs.counter) amount =
    match counter.resource with
    | Metric metric when Facts.is_home context frame.source ->
        context.call_amounts <-
          {
            call = Facts.quote frame.source site.origin;
            callee = path;
            states_cost = Option.is_some (Lazy.force method_cost) || list_metric_costs metric <> [];
            counts_potential =
              counts_provider_potential
              || (metric = Time && Option.is_some (Lazy.force method_cost))
              || List.exists (fun (cost : Mir.cost) -> cost.amortized) (list_metric_costs metric);
            counter;
            amount;
          }
          :: context.call_amounts
    | Metric _ | Calls _ -> ()
  in
  let after =
    Operations.spend_operation context after ~potential_change:(Some compute_change)
      ~note:note_amount (fun counter ->
        match (invocation.callee, counter.resource) with
        | Capability_method _, Calls _ ->
            Amounts.compute_step_amount context after invocation values counter
        | _ ->
            Amounts.compute_callee_amount ?method_cost:(Lazy.force method_cost) context after
              ~is_recursive:(Option.is_some recursive_callee) ~clauses:declared_clauses
              ~bind_frame:(fun clauses ->
                {
                  (read_entry_frame clauses) with
                  result = Some result;
                  condition = after.condition;
                })
              ~uses:invocation.uses ~values ~counts_provider_potential counter)
  in
  (after, Option.value !definition ~default:result)

let make_callback_cost (context : State.context) frame (metric : Language.Metric.t) (ty : Types.ty)
    term =
  let stated_by_type =
    match ty with
    | Types.Function { costs; _ } -> Costs.find_stated_operand costs metric
    | _ -> None
  in
  match stated_by_type with
  | Some stated -> stated
  | None ->
      let sort = Facts.declare_sort context ty in
      let symbol = Logic.Symbol.Callback_cost { metric; sort } in
      Facts.declare context (Logic.Function (symbol, [ sort ], Logic.Int));
      let cost = Logic.Apply (symbol, [ term ]) in
      let least = Costs.least_amount (Metric metric) in
      Facts.add_frame_fact context frame (Logic.less_equal least cost);
      let state_value value =
        Facts.add_frame_fact context frame (Logic.equal cost (Costs.larger least value))
      in
      (match term with
      | Logic.Symbol (Function_value { callee; _ }) ->
          Option.iter state_value
            (Option.bind (Contracts.read_signature context callee)
               (fun (signature : Types.signature) ->
                 Costs.find_stated_operand signature.costs metric))
      | _ -> ());
      (match List.assoc_opt (term, metric) context.lambda_costs with
      | Some (bound, showing) ->
          context.lambda_costs <- List.remove_assoc (term, metric) context.lambda_costs;
          context.obligations <- List.rev_append showing context.obligations;
          state_value bound
      | None -> ());
      cost

let compute_function_value_amount context frame ~location (function_type : Types.function_type)
    callee_term ~values (counter : Costs.counter) =
  let make_counted amount = Costs.make_counted_charge counter amount in
  let compute_call_amount metric =
    let make_cost () =
      make_callback_cost context frame metric (Types.Function function_type) callee_term
    in
    let make_plain amount = { Costs.amount; counted = No_potential } in
    match
      ( counter.amortized,
        Costs.list_stated_bounds function_type.costs metric ~amortized:true,
        counter.counting )
    with
    | true, Order_of :: _, Units -> { Costs.amount = Logic.int 1; counted = Potential_change }
    | _ -> (
        match
          (Costs.list_stated_bounds function_type.costs metric ~amortized:false, counter.counting)
        with
        | Order_of :: _, Units -> make_plain (Logic.int 1)
        | Exactly_cost amount :: _, (At_most | Exactly) -> make_plain (Logic.Integer amount)
        | _, (Units | At_most) ->
            make_plain (Amounts.compute_amount_within context frame counter (make_cost ()))
        | _, Exactly ->
            let cost = make_cost () in
            if cost <> Costs.zero then
              Facts.oblige
                ~holds_when:(Facts.find_counter_condition context counter)
                context frame location
                (Upper_bound_in_exact_cost { metric; call = { at = location; callee = None } })
                (Logic.equal cost Costs.zero);
            make_plain cost)
  in
  match counter.resource with
  | _ when counter.counting = Units && Amounts.passes_lambda_assuming_recursive_costs context values
    ->
      make_counted (Operations.declare_unknown_amount context frame counter)
  | Metric metric -> compute_call_amount metric
  | Calls (Through term) ->
      make_counted
        (if Amounts.lambda_captures_target context callee_term term then
           Operations.declare_unknown_amount context frame counter
         else
           Amounts.make_conditional_amount
             (Amounts.make_may_be_target context frame callee_term (Types.Function function_type)
                term)
             (Logic.int 1))
  | Calls (Capability capability | Capability_method (capability, _)) ->
      make_counted
        (Amounts.compute_capability_amount context frame ~uses:function_type.uses capability counter
           ~direct:(fun () -> Operations.declare_unknown_amount context frame counter))

type modelled =
  | By_contract of (State.frame * Logic.term)
  | Without_contract of (State.frame * Logic.term) option

let apply_call ?leave_lent context (frame : State.frame) (site : Invocation.site)
    (invocation : Invocation.t) ~through (values : State.passed list) =
  let location = Facts.locate context frame.source site.origin in
  (match context.panic_condition with
  | Some condition
    when (not context.panics)
         && Conditions.may_panic_for_every_value context.lookups ~current:context.current
              ~condition:context.condition invocation.uses ->
      Facts.oblige context frame location
        (Panics_where_ruled_out { call = { at = location; callee = None }; condition })
        (Logic.Boolean false)
  | Some _ | None -> ());
  List.iter
    (fun (passed : State.passed) ->
      match passed.shape with
      | Named_function { origin; path; _ } -> (
          match Contracts.find_function_contract context path with
          | Some contract ->
              Laws.check_named_callback context frame invocation passed ~origin path contract values
          | None -> ())
      | Forwarded local ->
          Validity.check_forwarded_callback context frame site invocation passed local values
      | Other ->
          Validity.check_callback_promises context frame ~location invocation passed
            ~unpromised:Nothing_promises ~assume:Validity.assume_nothing values
      | Lambda -> ())
    values;
  let declared_result_type = Facts.substitute_declared_type context frame site.type_ in
  let result_type = Types.erase_views declared_result_type in
  let is_update_step = calls_update_step context invocation in
  (match invocation.callee with
  | Intrinsic _ -> ()
  | _ ->
      List.iter
        (fun (passed : State.passed) ->
          if not (is_update_step && passed.position = 0) then
            Lambdas.check_valid context frame location passed.type_ passed.term ~deep:true
              ~moment:(When_passed { at = location; callee = None }))
        values);
  let havoc_whole_arguments frame =
    havoc_mut context frame values ~is_update_step ~list_modified:(fun _ -> None)
  in
  let list_arguments (type_arguments : Types.argument list) =
    List.map
      (fun argument ->
        match Types.substitute_argument_erased frame.substitution argument with
        | Types.Type ty -> Types.Type (Facts.substitute_type context frame ty)
        | other -> other)
      type_arguments
  in
  let list_capability_arguments (instantiation : Types.instantiation) =
    List.map
      (fun (name, argument) -> (name, Types.substitute_capabilities frame.substitution argument))
      instantiation.capability_arguments
  in
  let bind_callee path arguments capability_arguments ~fixed =
    let generics, capability_parameters =
      match Contracts.read_signature context path with
      | Some (signature : Types.signature) ->
          ( List.map (fun (generic : Types.generic) -> generic.generic) signature.generics,
            signature.capability_parameters )
      | None -> ([], [])
    in
    let rec bind_remaining substitution parameters arguments =
      match (parameters, arguments) with
      | parameter :: parameters, argument :: arguments ->
          bind_remaining (Types.bind_argument parameter argument substitution) parameters arguments
      | _ -> substitution
    in
    Types.combine_substitutions
      (bind_remaining fixed
         (List.filter
            (fun parameter -> Option.is_none (Types.find_argument parameter fixed))
            generics)
         arguments)
      (Types.make_capability_substitution capability_parameters capability_arguments)
  in
  let recursive_callee = Facts.find_recursive_callee context frame location invocation.callee in
  let with_contract ?(substitution_of = fun _ -> Types.no_substitution) ?(type_arguments = []) path
      = function
    | Some contract ->
        By_contract
          (call_contract ~recursive_callee ~lent_final:leave_lent context frame site invocation path
             contract values ~substitution_of ~type_arguments)
    | None ->
        let frame =
          havoc_mut context frame values ~is_update_step
            ~list_modified:(Contracts.list_modified_parts context path)
        in
        let frame =
          Operations.spend_operation context frame ~potential_change:None
            (Amounts.compute_step_amount context frame invocation values)
        in
        Without_contract (Some (frame, Facts.arrive context frame "result" result_type))
  in
  let modelled =
    match invocation.callee with
    | Function { path; instantiation } ->
        let arguments = list_arguments instantiation.type_arguments in
        let substitution =
          bind_callee path arguments
            (list_capability_arguments instantiation)
            ~fixed:Types.no_substitution
        in
        with_contract
          ~substitution_of:(fun _ -> substitution)
          ~type_arguments:arguments path
          (Contracts.find_function_contract context path)
    | Trait_method { trait; name; receiver; evidence; self_type; instantiation } -> (
        let arguments = list_arguments instantiation.type_arguments in
        let capability_arguments = list_capability_arguments instantiation in
        let evidence =
          Interface.Impls.resolve_evidence context.lookups.interface frame.substitution ~self_type
            ~trait evidence
        in
        let self_type = Facts.substitute_type context frame self_type in
        let trait = { trait with trait_arguments = list_arguments trait.trait_arguments } in
        Laws.assume_laws context frame trait self_type;
        let list_operands () = List.map (fun (passed : State.passed) -> passed.term) values in
        let trait_path = Path.Method { owner = trait.trait; name; receiver } in
        let method_ = Well_known.find_method trait_path in
        match (method_, evidence, list_operands ()) with
        | ( Some
              ( Fixed_width_integer_minimum_value | Fixed_width_integer_maximum_value
              | Fixed_width_integer_bit_width ),
            _,
            [] )
          when Types.find_integer_bits self_type <> None ->
            Without_contract
              (match
                 (method_, Types.find_integer_range self_type, Types.find_integer_bits self_type)
               with
              | Some Fixed_width_integer_minimum_value, Some (low, _), _ ->
                  Some (frame, Logic.Integer low)
              | Some Fixed_width_integer_maximum_value, Some (_, high), _ ->
                  Some (frame, Logic.Integer high)
              | Some Fixed_width_integer_bit_width, _, Some (bits, _) -> Some (frame, Logic.int bits)
              | _ -> None)
        | Some Equal_equal, _, [ left; right ] when Facts.is_equality_identity context self_type ->
            Without_contract (Some (frame, Logic.equal left right))
        | ( Some Equal_equal,
            (Impl { impl = Derived _; _ } | Derived_for_view { viewed = Derived _; _ }),
            [ left; right ] ) ->
            let spent =
              Operations.spend_operation context frame
                ~potential_change:
                  (Some
                     (fun () ->
                       Amounts.compute_call_potential_change context ~before:frame ~after:frame
                         values ~changed:[] ~result_type:declared_result_type
                         ~result:(Logic.equal left right)))
                (Amounts.compute_callee_amount
                   ~method_cost:(fun metric ->
                     Amounts.compute_method_cost context frame metric invocation.callee)
                   context frame ~is_recursive:false ~clauses:[]
                   ~bind_frame:(fun _ -> frame)
                   ~uses:invocation.uses ~values ~counts_provider_potential:false)
            in
            Without_contract
              (Some (spent, Operations.make_equality context frame self_type left right))
        | _ ->
            let trait_substitution =
              bind_callee trait_path arguments capability_arguments
                ~fixed:(Contracts.make_trait_substitution context.lookups trait self_type)
            in
            let path, callee_substitution =
              match evidence with
              | Impl { impl; substitution } | Derived_for_view { viewed = impl; substitution } ->
                  let path = Path.Method { owner = impl; name; receiver } in
                  (path, bind_callee path arguments capability_arguments ~fixed:substitution)
              | Bound -> (trait_path, trait_substitution)
            in
            let compute_substitution (clauses : State.clauses) =
              if clauses.inherited then trait_substitution else callee_substitution
            in
            let bind_restated subtrait restated =
              bind_callee restated arguments capability_arguments
                ~fixed:(Contracts.make_trait_substitution context.lookups subtrait self_type)
            in
            with_contract ~substitution_of:compute_substitution
              ~type_arguments:(Facts.list_method_type_arguments ~self_type arguments)
              path
              (Option.map
                 (add_restated_clauses context ~self_type ~bind:bind_restated trait.trait name
                    receiver)
                 (Contracts.find_method_contract context trait name receiver evidence)))
    | Indirect () ->
        Laws.check_callback_requires context frame site through values;
        let before = frame in
        let frame = havoc_whole_arguments frame in
        let result =
          match through with
          | Some (Types.Function function_type, callee_term, _)
            when Lambdas.is_in_the_logic function_type ->
              let term =
                Lambdas.apply_function context function_type callee_term
                  (List.map (fun (passed : State.passed) -> passed.term) values)
              in
              Facts.assume context frame (Facts.make_in_range result_type term);
              term
          | _ -> Facts.arrive context frame "result" result_type
        in
        Validity.assume_valid context frame result_type result;
        let frame =
          match through with
          | _ when context.counters = [] -> frame
          | Some (Types.Function function_type, callee_term, _) ->
              Operations.spend_operation context frame
                ~potential_change:
                  (Some
                     (fun () ->
                       Amounts.compute_call_potential_change context ~before ~after:frame values
                         ~changed:
                           (List.filter_map
                              (fun (passed : State.passed) ->
                                match (passed.mode, passed.passed_place) with
                                | Language.Mode.Mut, Some place ->
                                    Some (passed.position, place.read frame)
                                | _ -> None)
                              values)
                         ~result_type:declared_result_type ~result))
                (compute_function_value_amount context frame ~location function_type callee_term
                   ~values)
          | _ -> Operations.spend context frame (Operations.declare_unknown_amount context frame)
        in
        (match through with
        | Some (Types.Function function_type, callee_term, shape)
          when List.length function_type.inputs = List.length values -> (
            let entries = List.map (fun (passed : State.passed) -> passed.term) values in
            let exits =
              List.map
                (fun (passed : State.passed) ->
                  match (passed.mode, passed.passed_place) with
                  | Language.Mode.Mut, Some place -> place.read frame
                  | _ -> passed.term)
                values
            in
            Facts.assume context frame
              (Lambdas.make_callback_ensures context function_type callee_term ~entries ~exits
                 ~result);
            match shape with
            | Invocation.Forwarded local ->
                Validity.assume_own_callback_ensures context frame local ~entries ~exits ~result
            | Named_function _ | Lambda | Other -> ())
        | _ -> ());
        List.iter
          (fun (passed : State.passed) ->
            match (passed.mode, passed.passed_place) with
            | Language.Mode.Mut, Some place -> (
                try Validity.assume_valid context frame passed.type_ (place.read frame)
                with Facts.Unsupported _ -> ())
            | _ -> ())
          values;
        Without_contract (Some (frame, result))
    | Capability_method { capability; name } ->
        with_contract
          (Path.make_capability_method capability name)
          (Contracts.find_capability_contract context capability name)
    | Intrinsic { operation; type_arguments } ->
        let frame =
          match operation with
          | Lend _ -> frame
          | Scalar _ | Buffer _ | Runtime _ -> havoc_whole_arguments frame
        in
        let changed =
          List.map
            (fun (passed : State.passed) ->
              match (passed.mode, passed.passed_place) with
              | Language.Mode.Mut, Some place ->
                  Facts.read_or_arrive context frame "changed" passed.type_ place.read
              | _ -> passed.term)
            values
        in
        let types =
          List.filter_map
            (function Types.Type ty -> Some (Facts.substitute_type context frame ty) | _ -> None)
            type_arguments
        in
        let result =
          Intrinsics.translate_intrinsic context frame ~site operation types values ~changed
            result_type
        in
        let potential_change () =
          if Intrinsics.keeps_potential operation then Costs.zero
          else
            Amounts.compute_call_potential_change context ~before:frame ~after:frame values
              ~changed:
                (List.filter_map
                   (fun ((passed : State.passed), later) ->
                     if passed.mode = Language.Mode.Mut then Some (passed.position, later) else None)
                   (List.combine values changed))
              ~result_type:declared_result_type ~result
        in
        let frame =
          Operations.spend_operation context frame ~potential_change:(Some potential_change)
            (Amounts.compute_step_amount ~result context frame invocation values)
        in
        Without_contract (Some (frame, result))
  in
  match modelled with
  | By_contract (frame, result) -> Some (frame, result)
  | Without_contract result ->
      Facts.reject_uncompared_recursion context frame location recursive_callee;
      result
