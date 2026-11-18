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
    || match name with Logic.Symbol.Constant _ | Logic.Symbol.Text_literal _ -> true | _ -> false
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
  match clauses.callee.key with
  | Some key
    when frame.source.key = Some context.home
         && List.for_all is_fixed (Logic.list_free_constants term) ->
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
            Substituted
              {
                key;
                clause = clause.origin;
                replacements = List.filter_map Fun.id replacements;
                type_names;
              };
          ]
      else []
  | Some _ | None -> []

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

let evaluate_default_value (context : State.context) frame (clauses : State.clauses) position =
  match
    Option.bind clauses.callee.key (fun (key : Resolve.Names.key) ->
        Mir.read_defaults context.lookups.mir key.path)
  with
  | Some { form = Parameter_defaults defaults; _ } -> (
      match (List.assoc_opt position defaults, List.nth_opt clauses.parameters position) with
      | Some default, Some parameter ->
          snd
            (Amounts.run_code context frame default
               ~type_:(Facts.substitute_type context frame parameter.type_))
      | _ -> Facts.raise_bug "a parameter's default has no MIR")
  | Some { form = Field_defaults _; _ } | None ->
      Facts.raise_bug "a callee with no MIR of its defaults"

let is_datatype ty = match ty with Types.Named _ -> Types.find_builtin ty = None | _ -> false

let list_structural_parameters context (frame : State.frame) (clauses : State.clauses) =
  List.concat
    (List.mapi
       (fun index (parameter : Mir.parameter) ->
         match parameter.local with
         | Self -> (
             match (frame.old_self, frame.self_type) with
             | Some entry, Some ty when is_datatype ty -> [ (ty, entry, index) ]
             | _ -> [])
         | local -> (
             match
               ( Locals.find_opt (Core_local local) frame.old_locals,
                 Facts.find_local_type context frame (Core_local local) )
             with
             | Some entry, Some ty when is_datatype ty -> [ (ty, entry, index) ]
             | _ -> []))
       clauses.parameters)

let call_contract context (frame : State.frame) (site : Invocation.site) (invocation : Invocation.t)
    path (contract : State.contract) (values : State.passed list) ~recursive_callee ~lent_final
    ~havoc_mut ~substitution_of ~type_arguments =
  let is_logic_call = contract.is_logic_function && invocation.uses = Types.no_capabilities in
  let values =
    if is_logic_call then
      List.map
        (fun (passed : State.passed) ->
          if passed.mode = Types.Mut || Logic.mentions frame.bound passed.term then passed
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
      (fun index (parameter : Mir.parameter) ->
        let term =
          match find_argument_at index with
          | Some term -> Some term
          | None ->
              if parameter.has_default then
                let empty =
                  {
                    frame with
                    source = clauses.callee;
                    locals = Locals.empty;
                    types = Locals.empty;
                    makes_obligations = false;
                    substitution = substitution_of clauses;
                  }
                in
                Some (evaluate_default_value context empty clauses index)
              else None
        in
        (parameter, term))
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
    Option.map (fun (_, ty) -> Types.substitute (substitution_of clauses) ty) self
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
        let before = List.map (fun (ty, entry, _) -> Models.rank context ty entry) pairs in
        let after =
          List.map
            (fun (ty, _, index) -> Models.rank context ty (lookup_argument_at_index values index))
            pairs
        in
        Facts.oblige context frame Termination location
          [
            Text
              "This recursive call may not be on a part of its parameters: give the function a \
               `decreases` clause.";
          ]
          Logic.(
            conjunction
              (List.map (fun right_term -> Operation ("<=", [ int 0; right_term ])) before)
            &&& Amounts.compare_lexicographically before after)
    | ([], _ | _, []) when context.terminates ->
        Facts.oblige context frame Termination location
          [
            Text
              (if is_self_call then
                 "This recursive call may not end: give the function a `decreases` clause for the \
                  prover to show that the recursion ends."
               else
                 Printf.sprintf
                   "This call to `%s` may not end: it calls back here, and both need a `decreases` \
                    clause for the prover to show that the recursion ends."
                   (Facts.show_callee path));
          ]
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
        Facts.oblige context frame Termination location
          (State.Text "This call may not decrease `"
           :: List.concat
                (List.mapi
                   (fun index (measure : Mir.formula) ->
                     (if index = 0 then [] else [ State.Text ", " ])
                     @ [ Facts.quote caller measure.origin ])
                   measures)
          @ [ Text "`." ])
          (Amounts.compare_lexicographically before after)
    | [], _ | _, [] -> ()
    end;
  let precondition_clauses = Contracts.select_precondition_clauses contract in
  let required =
    let entry = read_entry_frame precondition_clauses in
    List.map
      (fun (requirement : Mir.requirement) ->
        let clause = requirement.clause in
        let _, term = Validity.read_specification context entry clause in
        let cited = Option.map (fun key -> (key, clause.origin)) precondition_clauses.callee.key in
        let fixes =
          list_required_fixes context frame precondition_clauses requirement term values
            ~type_names:(list_type_names (substitution_of precondition_clauses))
        in
        let message : State.message =
          [
            Text "`";
            Facts.quote precondition_clauses.callee clause.origin;
            Text (Printf.sprintf "` may not hold for this call to `%s`." (Facts.show_callee path));
          ]
        in
        Facts.oblige context frame Requires location ?cited ~fixes message term;
        term)
      precondition_clauses.requires
  in
  let required = Logic.conjunction required in
  let compute_required (clauses : State.clauses) =
    if clauses == precondition_clauses then required
    else
      Logic.conjunction
        (List.map
           (fun requirement ->
             snd (Validity.read_specification context (read_entry_frame clauses) requirement))
           (Facts.list_clauses clauses.requires))
  in
  let after = havoc_mut frame in
  let in_quantifier = is_logic_call && frame.binders <> [] in
  let state term =
    if in_quantifier then Facts.add_frame_fact context after term
    else Facts.assume context after term
  in
  let changed =
    List.filter_map
      (fun (passed : State.passed) ->
        match (passed.mode, passed.passed_place) with
        | Types.Mut, Some place ->
            Some
              (passed.position, Facts.read_or_arrive context after "changed" passed.type_ place.read)
        | _ -> None)
      values
  in
  let callee_bindings = list_bindings callee_clauses in
  let callee_arguments = List.filter_map snd callee_bindings in
  let is_on_bound_values = List.exists (Logic.mentions after.bound) callee_arguments in
  let result_type = Facts.substitute_type context frame site.type_ in
  let applied_as = ref None in
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
                  ((Interface.Impls.normalize context.lookups.interface
                      ~list_bounds:Interface.Impls.list_no_bounds)
                     (Types.substitute (substitution_of callee_clauses) parameter.type_)))
          callee_bindings
      in
      let result_sort = Facts.declare_sort context result_type in
      Facts.declare context (Logic.Function (function_symbol, sorts, result_sort));
      (match (path, callee_bindings) with
      | Method { name = "model"; receiver = Read; _ }, [ (self, _) ] when self.local = Self ->
          Models.rank_model context
            ((Interface.Impls.normalize context.lookups.interface
                ~list_bounds:Interface.Impls.list_no_bounds)
               (Types.substitute (substitution_of callee_clauses) self.type_))
            ~model:result_type function_symbol
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
    | `Lends, Some Types.Mut, Some leave ->
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
          ~when_:"when the lend of this part ends"
    | None -> ()
  in
  let is_updating_helper = Laws.calls_updating_helper context invocation in
  List.iter
    (fun (passed : State.passed) ->
      if passed.mode = Types.Mut && not (is_updating_helper && passed.position = 0) then
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
             let ty = Types.substitute (substitution_of callee_clauses) parameter.type_ in
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
                    [ (_, required, [ (_, Logic.Operation ("=", [ left; right ])) ]) ] ) -> (
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
                let none = Amounts.make_empty_parts context after result_type in
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
                | _, term -> state (Logic.( ==> ) (compute_required clauses) term)
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
    List.fold_left
      (fun total (passed : State.passed) ->
        let ty = passed.type_ in
        match passed.mode with
        | Types.Mut -> (
            match List.assoc_opt passed.position changed with
            | Some later ->
                Costs.plus total
                  (Costs.minus
                     (Amounts.compute_potential context after ty later)
                     (Amounts.compute_potential context frame ty passed.term))
            | None -> total)
        | Types.Own -> Costs.minus total (Amounts.compute_potential context frame ty passed.term)
        | Types.Read -> total)
      (match contract.result_kind with
      | `Lends -> (
          match lent_final with
          | Some leave ->
              Costs.minus
                (Amounts.compute_potential context after result_type result)
                (Amounts.compute_potential context after result_type (leave result))
          | None -> Costs.zero)
      | `Returns -> Amounts.compute_potential context after result_type result)
      values
  in
  let after =
    Operations.spend context after (fun counter ->
        match (invocation.callee, counter.resource) with
        | Capability_method _, Calls _ ->
            Amounts.compute_step_amount context after invocation values counter
        | _ ->
            let method_cost =
              if Laws.has_method_cost context invocation.callee path then
                Some
                  (fun metric -> Amounts.compute_method_cost context frame metric invocation.callee)
              else None
            in
            Amounts.compute_callee_amount ?method_cost context after
              ~is_recursive:(Option.is_some recursive_callee)
              ~clauses:(Contracts.list_declared_clauses contract)
              ~bind_frame:(fun clauses ->
                {
                  (read_entry_frame clauses) with
                  result = Some result;
                  condition = after.condition;
                })
              ~uses:(invocation.uses :> Types.capability list)
              ~values ~change:(Some compute_change) counter)
  in
  (after, result)

let make_callback_cost (context : State.context) frame (metric : Metric.t) (ty : Types.ty) term =
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
      Facts.add_frame_fact context frame (Logic.Operation ("<=", [ least; cost ]));
      let state_value value =
        Facts.add_frame_fact context frame (Logic.equal cost (Costs.larger least value))
      in
      (match term with
      | Logic.Symbol (Function_value { callee; _ }) ->
          Option.iter state_value
            (Option.bind (Interface.Impls.read_signature context.lookups.interface callee)
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
    callee_term (counter : Costs.counter) =
  let compute_call_amount metric =
    let make_cost () =
      make_callback_cost context frame metric (Types.Function function_type) callee_term
    in
    match (Costs.list_stated_bounds function_type.costs metric, counter.counting) with
    | Order_of :: _, Units -> Logic.int 1
    | Exactly_cost (Some amount) :: _, (At_most | Exactly) -> Logic.Integer amount
    | _, (Units | At_most) -> Amounts.compute_amount_within context frame counter (make_cost ())
    | _, Exactly ->
        let cost = make_cost () in
        if cost <> Costs.zero then
          Facts.oblige context frame Cost location
            [
              Text
                (Printf.sprintf
                   "Only an upper bound is known for the `%s` of this call, which may spend less, \
                    so no `==` bound can count it. State the cost with `<=`, or give the type of \
                    the function called an `==` bound."
                   (Metric.show metric));
            ]
            (Logic.equal cost Costs.zero);
        cost
  in
  match counter.resource with
  | Metric metric -> compute_call_amount metric
  | Calls (Through term) ->
      if Amounts.lambda_captures_target context callee_term term then
        Operations.declare_unknown_amount context frame counter
      else
        Amounts.make_conditional_amount
          (Amounts.make_may_be_target context frame callee_term (Types.Function function_type) term)
          (Logic.int 1)
  | Calls (Capability path | Capability_method (path, _)) ->
      if
        List.exists
          (function
            | Types.Capability used -> Path.equal used path
            | Types.Capability_parameter _ | Types.Capability_projection _
            | Types.Capability_variable _ ->
                true
            | Types.Capability_error _ ->
                Facts.raise_bug "the prover reads a capability with an error")
          (function_type.uses :> Types.capability list)
      then Operations.declare_unknown_amount context frame counter
      else Costs.zero

type modelled =
  | By_contract of (State.frame * Logic.term)
  | Without_contract of (State.frame * Logic.term) option

let apply_call ?leave_lent context (frame : State.frame) (site : Invocation.site)
    (invocation : Invocation.t) ~through (values : State.passed list) =
  let location = Facts.locate context frame.source site.origin in
  List.iter
    (fun (passed : State.passed) ->
      match passed.shape with
      | Named_function { origin; path; _ } -> (
          match Contracts.find_function_contract context.lookups path with
          | Some contract ->
              Laws.check_named_callback context frame invocation passed ~origin path contract values
          | None -> ())
      | Forwarded local ->
          Validity.check_forwarded_callback context frame site invocation passed local values
      | Other -> ())
    values;
  (match (invocation.lends, values) with
  | Some _, _ :: index :: _ -> Validity.note_place context frame site.origin (One index.term)
  | _ -> ());
  let result_type = Facts.substitute_type context frame site.type_ in
  (match invocation.callee with
  | Intrinsic _ -> ()
  | _ ->
      let exempt = Laws.calls_updating_helper context invocation in
      List.iter
        (fun (passed : State.passed) ->
          if not (exempt && passed.position = 0) then
            Lambdas.check_valid context frame location passed.type_ passed.term ~deep:true
              ~when_:"when it is passed to this call")
        values);
  let havoc_mut frame =
    List.fold_left
      (fun frame (passed : State.passed) ->
        match (passed.mode, passed.passed_place) with
        | Types.Mut, Some place ->
            place.write frame (Facts.arrive context frame "changed" passed.type_)
        | _ -> frame)
      frame values
  in
  let list_arguments (type_arguments : Types.argument list) =
    List.map
      (fun argument ->
        match Types.substitute_argument frame.substitution argument with
        | Types.Type ty -> Types.Type (Facts.substitute_type context frame ty)
        | other -> other)
      type_arguments
  in
  let list_capability_arguments (instantiation : Types.instantiation) =
    List.map
      (fun (name, argument) -> (name, Types.substitute_capabilities frame.substitution argument))
      instantiation.capability_arguments
  in
  let read_signature path = Interface.Impls.read_signature context.lookups.interface path in
  let list_generics path =
    match read_signature path with
    | Some (signature : Types.signature) ->
        List.map (fun (generic : Types.generic) -> generic.generic) signature.generics
    | None -> []
  in
  let list_capability_parameters path =
    match read_signature path with
    | Some (signature : Types.signature) -> signature.capability_parameters
    | None -> []
  in
  let bind_parameters parameters arguments ~fixed =
    let rec bind_remaining substitution parameters arguments =
      match (parameters, arguments) with
      | parameter :: parameters, argument :: arguments ->
          bind_remaining (Types.bind_argument parameter argument substitution) parameters arguments
      | _ -> substitution
    in
    bind_remaining fixed
      (List.filter
         (fun parameter -> Option.is_none (Types.find_argument parameter fixed))
         parameters)
      arguments
  in
  let resolution, recursive_callee =
    Facts.find_recursive_callee context frame location invocation.callee
  in
  let with_contract ?(substitution_of = fun _ -> Types.no_substitution) ?(type_arguments = []) path
      = function
    | Some contract ->
        By_contract
          (call_contract ~recursive_callee ~lent_final:leave_lent context frame site invocation path
             contract values ~havoc_mut ~substitution_of ~type_arguments)
    | None ->
        let frame = havoc_mut frame in
        let frame =
          Operations.spend context frame
            (Amounts.compute_step_amount context frame invocation values)
        in
        Without_contract (Some (frame, Facts.arrive context frame "result" result_type))
  in
  let modelled =
    match invocation.callee with
    | Function { path; instantiation } ->
        let arguments = list_arguments instantiation.type_arguments in
        let substitution =
          Types.combine_substitutions
            (bind_parameters (list_generics path) arguments ~fixed:Types.no_substitution)
            (Types.make_capability_substitution (list_capability_parameters path)
               (list_capability_arguments instantiation))
        in
        with_contract
          ~substitution_of:(fun _ -> substitution)
          ~type_arguments:arguments path
          (Contracts.find_function_contract context.lookups path)
    | Trait_method { trait; name; receiver; evidence; self_type; instantiation } -> (
        let arguments = list_arguments instantiation.type_arguments in
        let capability_arguments = list_capability_arguments instantiation in
        let self_type = Facts.substitute_type context frame self_type in
        let trait = { trait with trait_arguments = list_arguments trait.trait_arguments } in
        let evidence : Core.evidence =
          match (evidence, resolution.evidence) with
          | Bound, Some (Impl _ as resolved) -> resolved
          | _ -> evidence
        in
        Laws.assume_laws context frame ~at:location trait self_type;
        let list_operands () = List.map (fun (passed : State.passed) -> passed.term) values in
        match (name, evidence, list_operands ()) with
        | ("minimum_value" | "maximum_value" | "bit_width"), _, []
          when Well_known.is Fixed_width_integer trait.trait
               && Types.find_integer_bits self_type <> None ->
            Without_contract
              (match
                 (name, Types.find_integer_range self_type, Types.find_integer_bits self_type)
               with
              | "minimum_value", Some (low, _), _ -> Some (frame, Logic.Integer low)
              | "maximum_value", Some (_, high), _ -> Some (frame, Logic.Integer high)
              | _, _, Some (bits, _) -> Some (frame, Logic.int bits)
              | _ -> None)
        | "equal", _, [ left; right ]
          when Path.equal trait.trait Facts.equal_trait
               && Facts.is_equality_identity context self_type ->
            Without_contract (Some (frame, Logic.equal left right))
        | "equal", Impl { impl = Derived _; _ }, [ left; right ]
          when Path.equal trait.trait Facts.equal_trait ->
            Without_contract
              (Some (frame, Operations.make_equality context frame self_type left right))
        | _ ->
            (match evidence with
            | (Bound | Dynamic)
              when name = "from_template" && Path.equal trait.trait Laws.template_trait ->
                Facts.oblige context frame Requires location
                  [
                    Text
                      "A call of `from_template` through a bound or `any` cannot see the tag's \
                       `requires` on its template: build the value with a template, where the tag \
                       is known.";
                  ]
                  (Logic.Boolean false)
            | _ -> ());
            let trait_path = Path.Method { owner = trait.trait; name; receiver } in
            let trait_substitution =
              Types.combine_substitutions
                (bind_parameters (list_generics trait_path) arguments
                   ~fixed:(Contracts.make_trait_substitution context.lookups trait self_type))
                (Types.make_capability_substitution
                   (list_capability_parameters trait_path)
                   capability_arguments)
            in
            let path, callee_substitution =
              match evidence with
              | Impl { impl; substitution } ->
                  let impl_substitution =
                    Types.substitute_substitution frame.substitution substitution
                  in
                  let path = Path.Method { owner = impl; name; receiver } in
                  ( path,
                    Types.combine_substitutions
                      (bind_parameters (list_generics path) arguments ~fixed:impl_substitution)
                      (Types.make_capability_substitution (list_capability_parameters path)
                         capability_arguments) )
              | _ -> (trait_path, trait_substitution)
            in
            let compute_substitution (clauses : State.clauses) =
              if clauses.inherited then trait_substitution else callee_substitution
            in
            with_contract ~substitution_of:compute_substitution
              ~type_arguments:(Types.Type self_type :: arguments)
              path
              (Contracts.find_method_contract context.lookups trait name receiver evidence))
    | Indirect () ->
        Laws.check_callback_requires context frame site through values;
        let frame = havoc_mut frame in
        let frame =
          match through with
          | _ when context.counters = [] -> frame
          | Some (Types.Function function_type, callee_term, _) ->
              Operations.spend context frame
                (compute_function_value_amount context frame ~location function_type callee_term)
          | _ -> Operations.spend context frame (Operations.declare_unknown_amount context frame)
        in
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
        List.iter
          (fun (passed : State.passed) ->
            match (passed.mode, passed.passed_place) with
            | Types.Mut, Some place -> (
                try Validity.assume_valid context frame passed.type_ (place.read frame)
                with Facts.Unsupported _ -> ())
            | _ -> ())
          values;
        Without_contract (Some (frame, result))
    | Capability_method { capability; name } ->
        with_contract
          (Path.make_capability_method capability name)
          (Contracts.find_capability_contract context.lookups capability name)
    | Intrinsic { operation; type_arguments } ->
        let frame =
          match operation with
          | Lend _ -> frame
          | Scalar _ | Buffer _ | Runtime _ -> havoc_mut frame
        in
        let changed =
          List.map
            (fun (passed : State.passed) ->
              match (passed.mode, passed.passed_place) with
              | Types.Mut, Some place ->
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
        let frame =
          Operations.spend context frame
            (Amounts.compute_step_amount context frame invocation values)
        in
        Without_contract (Some (frame, result))
  in
  match modelled with
  | By_contract (frame, result) -> Some (frame, result)
  | Without_contract result ->
      Facts.reject_uncompared_recursion context frame location recursive_callee
        ~describe:
          (Printf.sprintf
             "This call to `%s` may not end: it calls back here, and the prover reads this call \
              without the callee's `decreases` clause.");
      result
