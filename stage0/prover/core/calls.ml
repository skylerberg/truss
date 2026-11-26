let lookup_argument_at_index (values : State.passed list) index =
  match
    List.find_map
      (fun (passed : State.passed) -> if passed.position = index then Some passed.term else None)
      values
  with
  | Some term -> term
  | None -> Logic.Boolean false

let name_term query ty term =
  let rec holds_call = function
    | Logic.Apply ((Logic.Symbol.Function _ | Logic.Symbol.Limited _), _) -> true
    | Logic.Forall (_, _, body) | Logic.Exists (_, body) -> holds_call body
    | term -> List.exists holds_call (Logic.list_arguments term)
  in
  if not (holds_call term) then term
  else
    let symbol = Logic.Symbol.Named_term term in
    let named = Logic.Symbol symbol in
    Query.run_once query (Value_of symbol) (fun () ->
        Query.declare query (Logic.Constant (symbol, Encoding.sort_of ty));
        Query.add_fact query (Logic.equal named term));
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

let havoc_mut (frame : State.frame) (values : State.passed list) ~list_modified =
  List.fold_left
    (fun havoc (passed : State.passed) ->
      let frame = havoc.after in
      match (passed.mode, passed.passed_place) with
      | Language.Mode.Mut, Some place ->
          let arrive ty = Encoding.arrive frame "changed" ty in
          let changed =
            Option.bind (list_modified passed.position) (fun parts ->
                List.fold_left
                  (fun whole (part : Types.modified) ->
                    Option.bind whole (fun whole ->
                        Encoding.replace_part frame.environment passed.type_ whole part.field_path
                          (fun part_type before ->
                            if part.is_elements then
                              Intrinsics.replace_elements frame part_type before
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

let call_contract (frame : State.frame) (site : Invocation.site) (callee : Callee.t)
    (definition : Callee.definition) (contract : State.contract) (values : State.passed list)
    ~recursive_callee =
  let path = definition.path and type_arguments = definition.type_arguments in
  let may_abort = Callee.may_abort frame.environment definition in
  let is_unspecified_application = may_abort && (frame : State.frame).is_ghost in
  let substitution_of = definition.substitution_of in
  let keep_holding_clauses clauses =
    Conditions.keep_holding frame.environment frame.query ~substitution:(substitution_of clauses)
      clauses
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
    contract.is_logic_function && Facts.remove_panic callee.uses = Types.no_capabilities
  in
  let values =
    if is_logic_call then
      List.map
        (fun (passed : State.passed) ->
          if passed.mode = Language.Mode.Mut || Logic.mentions frame.bound passed.term then passed
          else { passed with term = name_term frame.query passed.type_ passed.term })
        values
    else values
  in
  let location = Facts.locate frame site.origin in
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
      Termination.check_recursive_call frame location ~path callee_clauses
        ~is_self_call:(Path.equal recursive frame.environment.node)
        ~callee_entry:(read_entry_frame frame callee_clauses)
        ~argument_at:(lookup_argument_at_index values))
    recursive_callee;
  let precondition_clauses = Contracts.select_precondition_clauses contract in
  let read_required () =
    let entry =
      {
        (read_entry_frame frame precondition_clauses) with
        callees_whose_requires_are_read = path :: frame.callees_whose_requires_are_read;
      }
    in
    List.map
      (fun (requirement : Mir.requirement) ->
        let clause = requirement.clause in
        let _, term = Validity.read_specification entry clause in
        let cited = Some (precondition_clauses.callee.key, clause.origin) in
        let fixes =
          Fixes.list_required_fixes frame precondition_clauses requirement term values
            ~type_names:(Fixes.list_type_names (substitution_of precondition_clauses))
        in
        Obligations.oblige ?cited ~fixes ~holds_when:clause.holds_when frame location
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
    if List.exists (Path.equal path) frame.callees_whose_requires_are_read then Logic.Boolean true
    else Logic.conjunction (read_required ())
  in
  if not (frame.panics || Types.has_capability (Built_in Panic) callee.uses) then begin
    let clauses = contract.callee_clauses in
    let entry = read_entry_frame frame clauses in
    List.iter
      (fun (requirement : Mir.requirement) ->
        let _, term = Validity.read_specification entry requirement.clause in
        let fixes =
          Fixes.list_required_fixes frame clauses requirement term values
            ~type_names:(Fixes.list_type_names (substitution_of clauses))
        in
        let cited = Some (clauses.callee.key, requirement.clause.origin) in
        Obligations.oblige ?cited ~fixes frame location
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
             snd (Validity.read_specification (read_entry_frame base clauses) requirement))
           (Facts.list_clauses clauses.requires))
  in
  let callee_bindings = list_bindings callee_clauses in
  let callee_arguments = List.filter_map snd callee_bindings in
  let is_on_bound_values = List.exists (Logic.mentions frame.bound) callee_arguments in
  let declared_result_type = Encoding.substitute_declared_type frame site.type_ in
  let result_type = Types.erase_views declared_result_type in
  let defining_term = ref None in
  let list_modified = Contracts.list_modified_parts frame.environment path in
  let make_result (after : State.frame) =
    let applied =
      if is_logic_call && List.length callee_arguments = List.length callee_bindings then begin
        let sorts =
          List.mapi
            (fun index ((parameter : Mir.parameter), _) ->
              match
                List.find_opt (fun (passed : State.passed) -> passed.position = index) values
              with
              | Some passed -> Encoding.sort_of passed.type_
              | None ->
                  Encoding.sort_of
                    (Types.erase_views
                       ((Interface.Impls.normalize frame.environment.lookups.interface
                           ~list_bounds:frame.environment.bounds)
                          (Types.substitute (substitution_of callee_clauses) parameter.type_))))
            callee_bindings
        in
        let function_symbol =
          Contract_axioms.declare_function frame.query ~path ~type_arguments ~sorts ~result_type
        in
        (match (path, callee_bindings) with
        | Method { owner = Impl { trait; _ } as impl; name; receiver }, [ (self, _) ]
          when self.local = Self
               && Well_known.is_method Model_model (Method { owner = trait.path; name; receiver })
          ->
            Models.rank_model frame.environment frame.query
              (Types.erase_views
                 ((Interface.Impls.normalize frame.environment.lookups.interface
                     ~list_bounds:frame.environment.bounds)
                    (Types.substitute (substitution_of callee_clauses) self.type_)))
              ~model:result_type ~impl function_symbol
        | _ -> ());
        Some
          (Contract_axioms.apply after ~path ~type_arguments ~sorts ~result_type
             ~arguments:callee_arguments ~is_on_bound_values)
      end
      else None
    in
    let result =
      match applied with
      | Some application -> application.term
      | None -> Encoding.arrive after "result" result_type
    in
    if not is_unspecified_application then
      Validity.assume_valid (Facts.restrict_unless_proven after required) result_type result;
    (applied, result)
  in
  let assume_changed_validity (after : State.frame) ~changed ~left_valid =
    List.iter
      (fun (passed : State.passed) ->
        if passed.mode = Language.Mode.Mut then
          match List.assoc_opt passed.position changed with
          | Some term ->
              let valid =
                Validity.make_validity after ~assuming:true
                  ~includes_invariants:(not passed.is_step_self) passed.type_ term
              in
              Facts.assume after
                (match left_valid with Some left -> Logic.( ==> ) left valid | None -> valid)
          | None -> ())
      values
  in
  let instantiation_size =
    let size = ref 0 in
    List.iter
      (function
        | Types.Type argument ->
            ignore
              (Types.exists
                 (fun _ ->
                   incr size;
                   false)
                 argument)
        | Types.Value _ -> ())
      type_arguments;
    !size
  in
  let run_instantiating run =
    if
      List.for_all
        (fun (outer, outer_size) ->
          (not (Path.equal path outer)) || instantiation_size < outer_size)
        frame.instantiating
    then
      run (fun (entered : State.frame) ->
          { entered with instantiating = (path, instantiation_size) :: frame.instantiating })
  in
  let returns_where_its_condition_holds =
    (not may_abort)
    && not
         (Conditions.may_panic_for_every_value frame.environment.lookups
            ~current:frame.environment.current ~condition:frame.environment.condition callee.uses)
  in
  let state_axiom (after : State.frame) applied =
    if returns_where_its_condition_holds then
      Option.iter
        (fun application ->
          Contract_axioms.state after application contract ~substitution_of ~result_type
            ~group_member:callee.group_member ~is_on_bound_values)
        applied
  in
  let assume_ensures (base : State.frame) (after : State.frame) ~changed ~applied ~result ~final
      is_kept =
    let proves_the_axiom_domain = callee_clauses.panics_unless = [] || not frame.panics in
    let is_in_axiom (clauses : State.clauses) (clause : Mir.formula) =
      match applied with
      | Some (application : Contract_axioms.application) ->
          application.is_limited
          || proves_the_axiom_domain
             && Contract_axioms.states frame.query application clauses clause
      | None -> false
    in
    List.iter
      (fun ({ made_by = clauses; proven_under } : Contracts.promise) ->
        let exits =
          List.map
            (fun (position, entry) ->
              (position, Option.value (List.assoc_opt position changed) ~default:entry))
            arguments
        in
        let ensures_frame =
          {
            (Contracts.make_exit_frame base clauses ~entries:arguments ~exits ~result:(Some result)
               ~substitution:(substitution_of clauses))
            with
            condition = after.condition;
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
              match Validity.read_specification ensures_frame clause with
              | _, term ->
                  (match (applied, !defining_term) with
                  | Some application, None ->
                      defining_term := Contract_axioms.find_definition application term
                  | _ -> ());
                  Facts.assume after (Logic.( ==> ) (compute_required base proven_under) term)
              | exception Facts.Unsupported _ -> ())
          clauses.ensures)
      (Contracts.list_promises contract)
  in
  let assume_hypotheses (after : State.frame) applied =
    Option.iter
      (fun application ->
        Contract_axioms.assume_hypotheses after application ~arguments:callee_arguments)
      applied
  in
  let spend ~(before : State.frame) ~(after : State.frame) ~changed ~result ~final =
    Amounts.spend_contract_call ~before ~after site callee definition contract values ~changed
      ~result ~result_type:declared_result_type ~final
      ~is_recursive:(Option.is_some recursive_callee) ~bind_frame:(fun clauses ->
        { (read_entry_frame before clauses) with result = Some result; condition = after.condition })
  in
  let havoc = havoc_mut frame values ~list_modified in
  let after = havoc.after and changed = List.rev havoc.written in
  let applied, result = make_result after in
  (match result with
  | Logic.Apply (symbol, _) when is_unspecified_application ->
      Query.note_withheld frame.query symbol path
  | _ -> ());
  assume_changed_validity after ~changed ~left_valid:None;
  run_instantiating (fun enter ->
      state_axiom (enter after) applied;
      if not is_unspecified_application then
        match contract.result_kind with
        | `Lends ->
            let assume =
              assume_ensures (enter frame) (enter after) ~changed ~applied ~result
                ~final:(Some result)
            in
            assume Lending.holds_where_lent;
            assume (fun clause -> not (Lending.holds_where_lent clause))
        | `Returns ->
            assume_ensures (enter frame) (enter after) ~changed ~applied ~result ~final:None
              (fun _ -> true));
  if not is_unspecified_application then assume_hypotheses after applied;
  match (contract.result_kind, callee.lends) with
  | `Lends, Some Language.Mode.Mut ->
      havoc.end_writes after;
      let is_lender (position, _) = position = 0 in
      let where_lent = List.filter (fun changed -> not (is_lender changed)) changed in
      let end_lend (ended : State.frame) final =
        let havoc =
          havoc_mut ended
            (List.filter (fun (passed : State.passed) -> passed.position = 0) values)
            ~list_modified
        in
        let after = havoc.after and changed = List.rev havoc.written @ where_lent in
        assume_changed_validity after ~changed:(List.rev havoc.written)
          ~left_valid:
            (Some (Validity.make_validity after ~assuming:false ~deep:true result_type final));
        Validity.check_valid after location result_type final ~deep:true ~moment:When_lend_ends;
        run_instantiating (fun enter ->
            assume_ensures (enter ended) (enter after) ~changed ~applied ~result ~final:(Some final)
              (fun clause -> not (Lending.holds_where_lent clause)));
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

let apply_lend (frame : State.frame) (site : Invocation.site) (callee : Callee.t) ~through
    (values : State.passed list) =
  let location = Facts.locate frame site.origin in
  (match Obligations.find_ruled_out_panic frame with
  | Some condition
    when Conditions.may_panic_for_every_value frame.environment.lookups
           ~current:frame.environment.current ~condition:frame.environment.condition callee.uses ->
      Obligations.oblige frame location
        (Panics_where_ruled_out { call = { at = location; callee = None }; condition })
        (Logic.Boolean false)
  | Some _ | None -> ());
  let declared_result_type = Encoding.substitute_declared_type frame site.type_ in
  let result_type = Types.erase_views declared_result_type in
  (match callee.target with
  | Intrinsic _ -> ()
  | Definition _ | Function_value ->
      List.iter
        (fun (passed : State.passed) ->
          Validity.check_valid frame location passed.type_ passed.term ~deep:true
            ~includes_invariants:(not passed.is_step_self)
            ~moment:(When_passed { at = location; callee = None }))
        values);
  let havoc_whole_arguments frame = havoc_mut frame values ~list_modified:(fun _ -> None) in
  let recursive_callee = Termination.find_recursive_callee frame location callee.group_member in
  let call_definition (definition : Callee.definition) =
    match definition.contract with
    | Some contract ->
        By_contract (call_contract ~recursive_callee frame site callee definition contract values)
    | None -> (
        let list_modified = Contracts.list_modified_parts frame.environment definition.path in
        let havoc_and_spend frame =
          let havoc = havoc_mut frame values ~list_modified in
          let frame = Amounts.spend_call_without_a_contract havoc.after callee values in
          havoc.end_writes frame;
          frame
        in
        match callee.lends with
        | Some Language.Mode.Mut ->
            let frame = (havoc_mut frame values ~list_modified).after in
            Lent_without_contract
              {
                frame;
                result = Encoding.arrive frame "result" result_type;
                end_lend =
                  Some
                    (fun ended final ->
                      Validity.check_valid ended location result_type final ~deep:true
                        ~moment:When_lend_ends;
                      havoc_and_spend ended);
              }
        | Some (Read | Own) | None ->
            let frame = havoc_and_spend frame in
            Without_contract (Some (frame, Encoding.arrive frame "result" result_type)))
  in
  let modelled =
    match callee.target with
    | Definition
        ({ trait_method = Some { trait; self_type; evidence; name; receiver }; _ } as definition)
      -> (
        Laws.assume_laws frame trait self_type;
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
        | Some Equal_equal, _, [ left; right ]
          when Encoding.is_equality_identity frame.environment self_type ->
            Without_contract (Some (frame, Logic.equal left right))
        | ( Some Equal_equal,
            (Impl { impl = Derived _; _ } | Derived_for_view { viewed = Derived _; _ }),
            [ left; right ] ) ->
            let spent =
              Amounts.spend_derived_equality frame callee values ~result_type:declared_result_type
                ~result:(Logic.equal left right)
            in
            Without_contract (Some (spent, Operations.make_equality frame self_type left right))
        | _ -> call_definition definition)
    | Definition definition -> call_definition definition
    | Function_value ->
        let function_type, called =
          match through with
          | Some (Types.Function function_type, called) -> (function_type, called)
          | Some _ | None -> Facts.raise_bug "a call through a value that is not a function"
        in
        let entries = List.map (fun (passed : State.passed) -> passed.term) values in
        Callbacks.check_called frame site called entries;
        let before = frame in
        let is_defined = Logic.conjunction (Callbacks.list_called_requires before called entries) in
        let havoc = havoc_whole_arguments frame in
        let frame = havoc.after in
        let result =
          if Callbacks.is_in_the_logic function_type then begin
            let term = Callbacks.apply_function function_type called entries in
            Facts.assume
              (Facts.restrict_unless_proven frame is_defined)
              (Encoding.make_in_range result_type term);
            term
          end
          else Encoding.arrive frame "result" result_type
        in
        let is_unspecified_application =
          frame.is_ghost && not (Types.states_no_allocation function_type.costs)
        in
        if not is_unspecified_application then
          Validity.assume_valid (Facts.restrict_unless_proven frame is_defined) result_type result;
        let frame =
          Amounts.spend_indirect_call ~before ~after:frame ~location function_type called values
            ~changed:(List.rev havoc.written) ~result_type:declared_result_type ~result
        in
        if not is_unspecified_application then
          Callbacks.assume_returned
            (Facts.restrict_unless_proven frame is_defined)
            function_type called ~entries
            ~exits:(List.map (find_written havoc) values)
            ~result;
        List.iter
          (fun (passed : State.passed) ->
            Option.iter
              (Validity.assume_valid frame passed.type_)
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
            (function Types.Type ty -> Some (Encoding.substitute_type frame ty) | _ -> None)
            type_arguments
        in
        let result =
          Intrinsics.translate_intrinsic frame ~site operation types values ~changed result_type
        in
        let frame =
          Amounts.spend_intrinsic frame callee operation values ~changed
            ~result_type:declared_result_type ~result
        in
        havoc.end_writes frame;
        Without_contract (Some (frame, result))
  in
  match modelled with
  | By_contract applied -> Some applied
  | Without_contract returned ->
      Termination.reject_uncompared_recursion frame location recursive_callee;
      Option.map (fun (frame, result) -> { frame; result; end_lend = None }) returned
  | Lent_without_contract applied ->
      Termination.reject_uncompared_recursion frame location recursive_callee;
      Some applied

let apply_call (frame : State.frame) site callee ~through values =
  Option.map
    (fun { frame; result; _ } -> (frame, result))
    (apply_lend frame site callee ~through values)
