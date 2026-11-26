let lookup_argument_at_index (values : State.passed list) index =
  match
    List.find_map
      (fun (passed : State.passed) -> if passed.position = index then Some passed.term else None)
      values
  with
  | Some term -> term
  | None -> Logic.Boolean false

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
        Facts.declare context (Logic.Constant (symbol, Encoding.declare_sort context ty));
        Facts.add_fact context (Logic.equal named term));
    named

type applied = {
  frame : State.frame;
  result : Logic.term;
  end_lend : (State.frame -> Logic.term -> State.frame) option;
}

type havoc = {
  after : State.frame;
  written : (int * Logic.term) list;
  end_writes : State.frame -> unit;
}

let find_written havoc (passed : State.passed) =
  Option.value (List.assoc_opt passed.position havoc.written) ~default:passed.term

let havoc_mut context (frame : State.frame) (values : State.passed list) ~list_modified =
  List.fold_left
    (fun havoc (passed : State.passed) ->
      let frame = havoc.after in
      match (passed.mode, passed.passed_place) with
      | Language.Mode.Mut, Some place ->
          let arrive ty = Encoding.arrive context frame "changed" ty in
          let changed =
            Option.bind (list_modified passed.position) (fun parts ->
                List.fold_left
                  (fun whole (part : Types.modified) ->
                    Option.bind whole (fun whole ->
                        Encoding.replace_part context passed.type_ whole part.field_path
                          (fun part_type before ->
                            if part.is_elements then
                              Intrinsics.replace_elements context frame part_type before
                            else arrive part_type)))
                  (Some passed.term) parts)
          in
          let term = match changed with Some term -> term | None -> arrive passed.type_ in
          let after, end_write = place.write frame ~is_valid:(not passed.is_step_self) term in
          {
            after;
            written = (passed.position, term) :: havoc.written;
            end_writes =
              (fun ended ->
                havoc.end_writes ended;
                end_write ended);
          }
      | _ -> havoc)
    { after = frame; written = []; end_writes = ignore }
    values

let call_contract context (frame : State.frame) (site : Invocation.site) (callee : Callee.t)
    (definition : Callee.definition) (contract : State.contract) (values : State.passed list)
    ~recursive_callee =
  let path = definition.path and type_arguments = definition.type_arguments in
  let substitution_of (clauses : State.clauses) =
    Types.combine_substitutions (definition.substitution_of clauses) clauses.bindings
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
    contract.is_logic_function && Facts.remove_panic_condition callee.uses = Types.no_capabilities
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
  let arguments = List.map (fun (passed : State.passed) -> (passed.position, passed.term)) values in
  let read_entry_frame (base : State.frame) (clauses : State.clauses) =
    Contracts.make_entry_frame base clauses ~arguments ~substitution:(substitution_of clauses)
  in
  let callee_clauses = contract.callee_clauses in
  Option.iter
    (fun recursive ->
      Termination.check_recursive_call context frame location ~path callee_clauses
        ~is_self_call:(Path.equal recursive context.node)
        ~callee_entry:(read_entry_frame frame callee_clauses)
        ~argument_at:(lookup_argument_at_index values))
    recursive_callee;
  let precondition_clauses = Contracts.select_precondition_clauses contract in
  let read_required () =
    let entry = read_entry_frame frame precondition_clauses in
    List.map
      (fun (requirement : Mir.requirement) ->
        let clause = requirement.clause in
        let _, term = Validity.read_specification context entry clause in
        let cited = Some (precondition_clauses.callee.key, clause.origin) in
        let fixes =
          Fixes.list_required_fixes context frame precondition_clauses requirement term values
            ~type_names:(Fixes.list_type_names (substitution_of precondition_clauses))
        in
        Obligations.oblige ?cited ~fixes
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
    if List.exists (Path.equal path) context.callees_whose_requires_are_read then Logic.Boolean true
    else begin
      let outer = context.callees_whose_requires_are_read in
      context.callees_whose_requires_are_read <- path :: outer;
      Fun.protect
        ~finally:(fun () -> context.callees_whose_requires_are_read <- outer)
        (fun () -> Logic.conjunction (read_required ()))
    end
  in
  if not (Obligations.may_panic context || Types.has_capability (Built_in Panic) callee.uses) then begin
    let clauses = contract.callee_clauses in
    let entry = read_entry_frame frame clauses in
    List.iter
      (fun (requirement : Mir.requirement) ->
        let _, term = Validity.read_specification context entry requirement.clause in
        let fixes =
          Fixes.list_required_fixes context frame clauses requirement term values
            ~type_names:(Fixes.list_type_names (substitution_of clauses))
        in
        let cited = Some (clauses.callee.key, requirement.clause.origin) in
        Obligations.oblige ?cited ~fixes context frame location
          (Precondition_may_panic
             {
               clause = Facts.quote clauses.callee requirement.clause.origin;
               call = { at = location; callee = Some path };
             })
          term)
      clauses.panics_unless
  end;
  let compute_required (base : State.frame) (clauses : State.clauses) =
    if clauses == precondition_clauses then required
    else
      Logic.conjunction
        (List.map
           (fun requirement ->
             snd (Validity.read_specification context (read_entry_frame base clauses) requirement))
           (Facts.list_clauses clauses.requires))
  in
  let in_quantifier = is_logic_call && frame.binders <> [] in
  let callee_bindings = list_bindings callee_clauses in
  let callee_arguments = List.filter_map snd callee_bindings in
  let is_on_bound_values = List.exists (Logic.mentions frame.bound) callee_arguments in
  let declared_result_type = Encoding.substitute_declared_type context frame site.type_ in
  let result_type = Types.erase_views declared_result_type in
  let defining_term = ref None in
  let list_modified = Contracts.list_modified_parts context path in
  let make_result (after : State.frame) =
    let applied =
      if is_logic_call && List.length callee_arguments = List.length callee_bindings then begin
        let sorts =
          List.mapi
            (fun index ((parameter : Mir.parameter), _) ->
              match
                List.find_opt (fun (passed : State.passed) -> passed.position = index) values
              with
              | Some passed -> Encoding.declare_sort context passed.type_
              | None ->
                  Encoding.declare_sort context
                    (Types.erase_views
                       ((Interface.Impls.normalize context.lookups.interface
                           ~list_bounds:context.bounds)
                          (Types.substitute (substitution_of callee_clauses) parameter.type_))))
            callee_bindings
        in
        let function_symbol =
          Contract_axioms.declare_function context ~path ~type_arguments ~sorts ~result_type
        in
        (match (path, callee_bindings) with
        | Method { owner = Impl { trait; _ } as impl; name; receiver }, [ (self, _) ]
          when self.local = Self
               && Well_known.is_method Model_model (Method { owner = trait.path; name; receiver })
          ->
            Models.rank_model context
              (Types.erase_views
                 ((Interface.Impls.normalize context.lookups.interface ~list_bounds:context.bounds)
                    (Types.substitute (substitution_of callee_clauses) self.type_)))
              ~model:result_type ~impl function_symbol
        | _ -> ());
        Some
          (Contract_axioms.apply context after ~path ~type_arguments ~sorts ~result_type
             ~arguments:callee_arguments ~is_on_bound_values)
      end
      else None
    in
    let result =
      match applied with
      | Some application -> application.term
      | None -> Encoding.arrive context after "result" result_type
    in
    Validity.assume_valid context after result_type result;
    (applied, result)
  in
  let assume_changed_validity (after : State.frame) ~changed ~left_valid =
    List.iter
      (fun (passed : State.passed) ->
        if passed.mode = Language.Mode.Mut then
          match List.assoc_opt passed.position changed with
          | Some term ->
              let valid =
                Validity.make_validity context after ~assuming:true
                  ~includes_invariants:(not passed.is_step_self) passed.type_ term
              in
              Facts.assume context after
                (match left_valid with Some left -> Logic.( ==> ) left valid | None -> valid)
          | None -> ())
      values
  in
  let run_instantiating run =
    if not (List.exists (Path.equal path) context.instantiating) then begin
      context.instantiating <- path :: context.instantiating;
      Fun.protect ~finally:(fun () -> context.instantiating <- List.tl context.instantiating) run
    end
  in
  let state_axiom (after : State.frame) applied =
    Option.iter
      (fun application ->
        Contract_axioms.state context after application contract ~substitution_of ~result_type
          ~group_member:callee.group_member ~is_on_bound_values)
      applied
  in
  let assume_ensures (base : State.frame) (after : State.frame) ~changed ~applied ~result ~final
      is_kept =
    let is_in_axiom (clauses : State.clauses) (clause : Mir.formula) =
      match applied with
      | Some (application : Contract_axioms.application) ->
          application.is_limited || Contract_axioms.states context application clauses clause
      | None -> false
    in
    let state term =
      if in_quantifier then Facts.add_frame_fact context after term
      else Facts.assume context after term
    in
    List.iter
      (fun (clauses : State.clauses) ->
        let exits =
          List.map
            (fun (position, entry) ->
              (position, Option.value (List.assoc_opt position changed) ~default:entry))
            arguments
        in
        let is_unbound_in_quantifier = in_quantifier && not is_on_bound_values in
        let ensures_frame =
          {
            (Contracts.make_exit_frame base clauses ~entries:arguments ~exits ~result:(Some result)
               ~substitution:(substitution_of clauses))
            with
            condition = (if is_unbound_in_quantifier then Logic.Boolean true else after.condition);
            bound = (if is_unbound_in_quantifier then [] else base.bound);
            binders = (if is_unbound_in_quantifier then [] else base.binders);
          }
        in
        let ensures_frame =
          match final with
          | Some final -> Lending.bind_final ensures_frame final
          | None -> ensures_frame
        in
        List.iter
          (fun (clause : Mir.formula) ->
            if is_kept clause && not (is_in_axiom clauses clause) then
              match Validity.read_specification context ensures_frame clause with
              | _, term ->
                  (match (applied, !defining_term) with
                  | Some application, None ->
                      defining_term := Contract_axioms.find_definition application term
                  | _ -> ());
                  state (Logic.( ==> ) (compute_required base clauses) term)
              | exception Facts.Unsupported _ -> ())
          clauses.ensures)
      (Contracts.list_declared_clauses contract)
  in
  let assume_hypotheses (after : State.frame) applied =
    Option.iter
      (fun application ->
        Contract_axioms.assume_hypotheses context after application ~arguments:callee_arguments)
      applied
  in
  let spend ~(before : State.frame) ~(after : State.frame) ~changed ~result ~final =
    Amounts.spend_contract_call context ~before ~after site callee definition contract values
      ~changed ~result ~result_type:declared_result_type ~final
      ~is_recursive:(Option.is_some recursive_callee) ~bind_frame:(fun clauses ->
        { (read_entry_frame before clauses) with result = Some result; condition = after.condition })
  in
  let havoc = havoc_mut context frame values ~list_modified in
  let after = havoc.after and changed = List.rev havoc.written in
  let applied, result = make_result after in
  assume_changed_validity after ~changed ~left_valid:None;
  run_instantiating (fun () ->
      state_axiom after applied;
      match contract.result_kind with
      | `Lends ->
          let assume = assume_ensures frame after ~changed ~applied ~result ~final:(Some result) in
          assume Lending.holds_where_lent;
          assume (fun clause -> not (Lending.holds_where_lent clause))
      | `Returns -> assume_ensures frame after ~changed ~applied ~result ~final:None (fun _ -> true));
  assume_hypotheses after applied;
  match (contract.result_kind, callee.lends) with
  | `Lends, Some Language.Mode.Mut ->
      havoc.end_writes after;
      let end_lend (ended : State.frame) final =
        let havoc = havoc_mut context ended values ~list_modified in
        let after = havoc.after and changed = List.rev havoc.written in
        assume_changed_validity after ~changed
          ~left_valid:
            (Some
               (Validity.make_validity context after ~assuming:false ~deep:true result_type final));
        Validity.check_valid context after location result_type final ~deep:true
          ~moment:When_lend_ends;
        run_instantiating (fun () ->
            assume_ensures ended after ~changed ~applied ~result ~final:(Some final) (fun clause ->
                not (Lending.holds_where_lent clause)));
        let after = spend ~before:ended ~after ~changed ~result ~final:(Some final) in
        havoc.end_writes after;
        after
      in
      {
        frame = after;
        result = Option.value !defining_term ~default:result;
        end_lend = Some end_lend;
      }
  | (`Lends | `Returns), _ ->
      let after = spend ~before:frame ~after ~changed ~result ~final:None in
      havoc.end_writes after;
      { frame = after; result = Option.value !defining_term ~default:result; end_lend = None }

type modelled =
  | By_contract of applied
  | Without_contract of (State.frame * Logic.term) option
  | Lent_without_contract of applied

let apply_lend context (frame : State.frame) (site : Invocation.site) (callee : Callee.t) ~through
    (values : State.passed list) =
  let location = Facts.locate context frame.source site.origin in
  (match Obligations.find_ruled_out_panic context with
  | Some condition
    when Conditions.may_panic_for_every_value context.lookups ~current:context.current
           ~condition:context.condition callee.uses ->
      Obligations.oblige context frame location
        (Panics_where_ruled_out { call = { at = location; callee = None }; condition })
        (Logic.Boolean false)
  | Some _ | None -> ());
  List.iter
    (fun (passed : State.passed) ->
      match passed.shape with
      | Named_function { origin; path; _ } -> (
          match Contracts.find_function_contract context path with
          | Some contract ->
              Callbacks.check_named_callback context frame callee passed ~origin path contract
                values
          | None -> ())
      | Forwarded local ->
          Callbacks.check_forwarded_callback context frame site callee passed local values
      | Other ->
          Callbacks.check_callback_promises context frame ~location callee passed
            ~unpromised:Nothing_promises ~assume:Callbacks.assume_nothing values
      | Lambda -> ())
    values;
  let declared_result_type = Encoding.substitute_declared_type context frame site.type_ in
  let result_type = Types.erase_views declared_result_type in
  (match callee.target with
  | Intrinsic _ -> ()
  | Definition _ | Function_value ->
      List.iter
        (fun (passed : State.passed) ->
          Validity.check_valid context frame location passed.type_ passed.term ~deep:true
            ~includes_invariants:(not passed.is_step_self)
            ~moment:(When_passed { at = location; callee = None }))
        values);
  let havoc_whole_arguments frame = havoc_mut context frame values ~list_modified:(fun _ -> None) in
  let recursive_callee =
    Termination.find_recursive_callee context frame location callee.group_member
  in
  let call_definition (definition : Callee.definition) =
    match definition.contract with
    | Some contract ->
        By_contract
          (call_contract ~recursive_callee context frame site callee definition contract values)
    | None -> (
        let list_modified = Contracts.list_modified_parts context definition.path in
        let havoc_and_spend frame =
          let havoc = havoc_mut context frame values ~list_modified in
          let frame = Amounts.spend_call_without_a_contract context havoc.after callee values in
          havoc.end_writes frame;
          frame
        in
        match callee.lends with
        | Some Language.Mode.Mut ->
            let frame = (havoc_mut context frame values ~list_modified).after in
            Lent_without_contract
              {
                frame;
                result = Encoding.arrive context frame "result" result_type;
                end_lend =
                  Some
                    (fun ended final ->
                      Validity.check_valid context ended location result_type final ~deep:true
                        ~moment:When_lend_ends;
                      havoc_and_spend ended);
              }
        | Some (Read | Own) | None ->
            let frame = havoc_and_spend frame in
            Without_contract (Some (frame, Encoding.arrive context frame "result" result_type)))
  in
  let modelled =
    match callee.target with
    | Definition
        ({ trait_method = Some { trait; self_type; evidence; name; receiver }; _ } as definition)
      -> (
        Laws.assume_laws context frame trait self_type;
        let operands = List.map (fun (passed : State.passed) -> passed.term) values in
        let method_ =
          Well_known.find_method (Path.Method { owner = trait.trait; name; receiver })
        in
        match (method_, evidence, operands) with
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
        | Some Equal_equal, _, [ left; right ] when Encoding.is_equality_identity context self_type
          ->
            Without_contract (Some (frame, Logic.equal left right))
        | ( Some Equal_equal,
            (Impl { impl = Derived _; _ } | Derived_for_view { viewed = Derived _; _ }),
            [ left; right ] ) ->
            let spent =
              Amounts.spend_derived_equality context frame callee values
                ~result_type:declared_result_type ~result:(Logic.equal left right)
            in
            Without_contract
              (Some (spent, Operations.make_equality context frame self_type left right))
        | _ -> call_definition definition)
    | Definition definition -> call_definition definition
    | Function_value ->
        Callbacks.check_callback_requires context frame site through values;
        let before = frame in
        let havoc = havoc_whole_arguments frame in
        let frame = havoc.after in
        let result =
          match through with
          | Some (Types.Function function_type, callee_term, _)
            when Callbacks.is_in_the_logic function_type ->
              let term =
                Callbacks.apply_function context function_type callee_term
                  (List.map (fun (passed : State.passed) -> passed.term) values)
              in
              Facts.assume context frame (Encoding.make_in_range result_type term);
              term
          | _ -> Encoding.arrive context frame "result" result_type
        in
        Validity.assume_valid context frame result_type result;
        let frame =
          Amounts.spend_indirect_call context ~before ~after:frame ~location through values
            ~changed:(List.rev havoc.written) ~result_type:declared_result_type ~result
        in
        (match through with
        | Some (Types.Function function_type, callee_term, shape)
          when List.length function_type.inputs = List.length values -> (
            let entries = List.map (fun (passed : State.passed) -> passed.term) values in
            let exits = List.map (find_written havoc) values in
            Facts.assume context frame
              (Callbacks.make_callback_ensures context function_type callee_term ~entries ~exits
                 ~result);
            match shape with
            | Invocation.Forwarded local ->
                Callbacks.assume_own_callback_ensures context frame local ~entries ~exits ~result
            | Named_function _ | Lambda | Other -> ())
        | _ -> ());
        List.iter
          (fun (passed : State.passed) ->
            Option.iter
              (Validity.assume_valid context frame passed.type_)
              (List.assoc_opt passed.position havoc.written))
          values;
        havoc.end_writes frame;
        Without_contract (Some (frame, result))
    | Intrinsic { operation; type_arguments } ->
        let havoc =
          match operation with
          | Lend _ -> { after = frame; written = []; end_writes = ignore }
          | Scalar _ | Buffer _ | Runtime _ -> havoc_whole_arguments frame
        in
        let frame = havoc.after in
        let changed = List.map (find_written havoc) values in
        let types =
          List.filter_map
            (function
              | Types.Type ty -> Some (Encoding.substitute_type context frame ty) | _ -> None)
            type_arguments
        in
        let result =
          Intrinsics.translate_intrinsic context frame ~site operation types values ~changed
            result_type
        in
        let frame =
          Amounts.spend_intrinsic context frame callee operation values ~changed
            ~result_type:declared_result_type ~result
        in
        havoc.end_writes frame;
        Without_contract (Some (frame, result))
  in
  match modelled with
  | By_contract applied -> Some applied
  | Without_contract returned ->
      Termination.reject_uncompared_recursion context frame location recursive_callee;
      Option.map (fun (frame, result) -> { frame; result; end_lend = None }) returned
  | Lent_without_contract applied ->
      Termination.reject_uncompared_recursion context frame location recursive_callee;
      Some applied

let apply_call context frame site callee ~through values =
  Option.map
    (fun { frame; result; _ } -> (frame, result))
    (apply_lend context frame site callee ~through values)
