let make_state () : State.axiom_state =
  {
    axiomatizing = [];
    open_axioms = [];
    axioms_of = Tables.Symbol_table.create 16;
    axiom_clauses = Tables.Axiom_clause_table.create 16;
  }

let find_innermost_axiom (context : State.context) (frame : State.frame) term =
  match context.axioms.open_axioms with
  | axiom :: _
    when let named = List.filter (fun name -> Logic.mentions [ name ] term) frame.bound in
         named <> [] && List.for_all (fun name -> List.mem name axiom.parameters) named ->
      Some axiom
  | _ -> None

let assume_typed context (frame : State.frame) term =
  let guarded = Logic.( ==> ) frame.condition term in
  match find_innermost_axiom context frame guarded with
  | Some axiom -> axiom.hypotheses <- guarded :: axiom.hypotheses
  | None -> Facts.assume context frame term

let rec map_each_value context (frame : State.frame) value make =
  if not (Logic.mentions frame.bound value) then make frame value
  else
    match find_innermost_axiom context frame value with
    | Some axiom ->
        axiom.at_calls <-
          (fun frame substitute -> map_each_value context frame (substitute value) make)
          :: axiom.at_calls
    | None -> ()

type application = {
  symbol : Logic.symbol;
  sorts : Logic.sort list;
  term : Logic.term;
  is_limited : bool;
}

let declare_function context ~path ~type_arguments ~sorts ~result_type =
  let symbol = Logic.Symbol.Function { callee = path; type_arguments } in
  let result_sort = Facts.declare_sort context result_type in
  Facts.declare context (Logic.Function (symbol, sorts, result_sort));
  symbol

let make_numbered_parameters label sorts =
  List.mapi (fun index sort -> (Logic.Symbol.Variable { label; numbers = [ index ] }, sort)) sorts

let apply (context : State.context) (frame : State.frame) ~path ~type_arguments ~sorts ~result_type
    ~arguments ~is_on_bound_values =
  let function_symbol = Logic.Symbol.Function { callee = path; type_arguments } in
  let is_limited = List.mem function_symbol context.axioms.axiomatizing in
  let symbol =
    if is_limited then begin
      let limited = Logic.Symbol.Limited { callee = path; type_arguments } in
      Facts.declare context
        (Logic.Function (limited, sorts, Facts.declare_sort context result_type));
      Facts.run_once context (Limited_link function_symbol) (fun () ->
          let parameters = make_numbered_parameters "linked" sorts in
          let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
          let applied = Logic.Apply (function_symbol, inputs) in
          Facts.add_fact context
            (Logic.forall ~trigger:[ applied ]
               (parameters, Logic.equal applied (Logic.Apply (limited, inputs)))));
      limited
    end
    else function_symbol
  in
  let term = Logic.Apply (symbol, arguments) in
  Facts.assume context frame (Facts.make_in_range result_type term);
  if Facts.find_bounds result_type <> None && is_on_bound_values then
    Facts.run_once context (In_range symbol) (fun () ->
        let parameters = make_numbered_parameters "ranged" sorts in
        Facts.add_fact context
          (Logic.forall
             ( parameters,
               Facts.make_in_range result_type
                 (Logic.Apply (symbol, List.map (fun (name, _) -> Logic.Symbol name) parameters)) )));
  { symbol; sorts; term; is_limited }

let make_fresh_parameters (context : State.context) label sorts =
  let axiom = Query.take_fresh_number context.query in
  List.mapi
    (fun index sort -> (Logic.Symbol.Variable { label; numbers = [ axiom; index ] }, sort))
    sorts

let find_readable_clause context mark clause inside =
  match snd (Validity.read_specification context inside clause) with
  | term when not (Facts.mentions_fresh_after context mark term) -> Some term
  | _ -> None
  | exception Facts.Unsupported _ -> None

let axiomatize (context : State.context) symbol parameters make =
  let mark = Query.count_fresh context.query in
  let axiom = { State.parameters = List.map fst parameters; hypotheses = []; at_calls = [] } in
  let open_axioms = context.axioms.open_axioms in
  context.axioms.axiomatizing <- symbol :: context.axioms.axiomatizing;
  context.axioms.open_axioms <- axiom :: open_axioms;
  Fun.protect
    ~finally:(fun () ->
      context.axioms.axiomatizing <- List.tl context.axioms.axiomatizing;
      context.axioms.open_axioms <- open_axioms)
    (fun () ->
      let stated, newest_facts = Query.run_in_scope context.query (List.map fst parameters) make in
      let drop_fresh_terms terms =
        List.filter
          (fun term -> not (Facts.mentions_fresh_after context mark term))
          (List.rev terms)
      in
      axiom.hypotheses <- drop_fresh_terms axiom.hypotheses;
      (stated, Logic.conjunction (drop_fresh_terms newest_facts), axiom))

let find_smaller_than_entry (context : State.context) (callee_clauses : State.clauses) ~group_member
    ~callee_entry ~inputs =
  match group_member with
  | None -> Some (Logic.Boolean true)
  | Some member ->
      Termination.find_induction_premise context callee_clauses
        ~is_self_call:(Path.equal member context.node) ~callee_entry ~argument_at:(List.nth inputs)

let state_with_trigger (context : State.context) (outer : State.frame) (application : application)
    (contract : State.contract) ~substitution_of ~result_type ~group_member ~is_triggered =
  let symbol = application.symbol and sorts = application.sorts in
  let callee_clauses = contract.callee_clauses in
  Facts.run_once context (Contract_of symbol) (fun () ->
      let parameters = make_fresh_parameters context "ensured" sorts in
      let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
      let arguments = List.mapi (fun index input -> (index, input)) inputs in
      let applied = Logic.Apply (symbol, inputs) in
      let outside =
        {
          outer with
          bound = List.map fst parameters;
          binders = [];
          condition = Logic.Boolean true;
          makes_obligations = false;
        }
      in
      let bind (clauses : State.clauses) =
        Validity.bind_arguments outside clauses ~arguments ~substitution:(substitution_of clauses)
      in
      let mark = Query.count_fresh context.query in
      let stated, facts, axiom =
        axiomatize context symbol parameters (fun () ->
            let valid =
              Logic.conjunction
                (List.map2
                   (fun (parameter : Mir.parameter) input ->
                     let ty =
                       Types.substitute_erased (substitution_of callee_clauses) parameter.type_
                     in
                     Logic.( &&& ) (Facts.make_in_range ty input)
                       (Validity.make_validity context outside ~assuming:true ty input))
                   callee_clauses.parameters inputs)
            in
            let smaller =
              find_smaller_than_entry context callee_clauses ~group_member
                ~callee_entry:(bind callee_clauses) ~inputs
            in
            let readable_clauses =
              List.filter_map
                (fun (clauses : State.clauses) ->
                  let inside =
                    { (bind clauses) with result = Some applied; makes_obligations = false }
                  in
                  let required =
                    List.map
                      (fun requirement -> find_readable_clause context mark requirement inside)
                      (Facts.list_clauses clauses.requires)
                  in
                  if List.mem None required then None
                  else
                    match
                      List.filter_map
                        (fun (clause : Mir.formula) ->
                          Option.map
                            (fun term -> (clause, term))
                            (find_readable_clause context mark clause inside))
                        clauses.ensures
                    with
                    | [] -> None
                    | ensures -> Some (clauses, List.filter_map Fun.id required, ensures))
                (Contracts.list_declared_clauses contract)
            in
            match smaller with
            | Some smaller ->
                let premise = Logic.( &&& ) valid smaller in
                if readable_clauses = [] || Facts.mentions_fresh_after context mark premise then
                  None
                else Some (premise, readable_clauses)
            | None -> None)
      in
      match stated with
      | None -> ()
      | Some (premise, readable_clauses) -> (
          let has_quantifier_through_definitions body =
            Logic.has_quantifier body
            || Logic.mentions (Query.list_defined_symbols context.query) body
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
                    Tables.Axiom_clause_table.replace context.axioms.axiom_clauses
                      (symbol, clauses.callee.key, clauses.callee.definition, clause.origin)
                      ())
                  ensures)
              readable_clauses;
          Tables.Symbol_table.add context.axioms.axioms_of symbol axiom;
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
                         (Logic.conjunction ((premise :: axiom.hypotheses) @ required))
                         body
                         (Logic.Apply (unspecified, inputs));
                   })
          | None ->
              Facts.add_fact context
                (Logic.forall
                   ~trigger:(if is_triggered then [ applied ] else [])
                   ( parameters,
                     Logic.( ==> )
                       (Logic.conjunction (premise :: axiom.hypotheses))
                       (Logic.conjunction
                          (facts
                          :: List.map
                               (fun (_, required, ensures) ->
                                 Logic.( ==> ) (Logic.conjunction required)
                                   (Logic.conjunction (List.map snd ensures)))
                               readable_clauses)) ))))

let state context outer (application : application) (contract : State.contract) ~substitution_of
    ~result_type ~group_member ~is_on_bound_values =
  let add =
    state_with_trigger context outer application contract ~substitution_of ~result_type
      ~group_member
  in
  if not application.is_limited then
    if contract.result_kind = `Returns && not (Types.equal result_type Types.unit) then
      add ~is_triggered:true
    else if is_on_bound_values then add ~is_triggered:false

let states (context : State.context) (application : application) (clauses : State.clauses)
    (clause : Mir.formula) =
  Tables.Axiom_clause_table.mem context.axioms.axiom_clauses
    (application.symbol, clauses.callee.key, clauses.callee.definition, clause.origin)

let assume_hypotheses (context : State.context) (frame : State.frame) (application : application)
    ~arguments =
  if not application.is_limited then
    List.iter
      (fun (axiom : State.open_axiom) ->
        let substitute = Logic.substitute (List.combine axiom.parameters arguments) in
        List.iter
          (fun hypothesis -> assume_typed context frame (substitute hypothesis))
          axiom.hypotheses;
        List.iter (fun apply_hook -> apply_hook frame substitute) axiom.at_calls)
      (Tables.Symbol_table.find_all context.axioms.axioms_of application.symbol)

let rec has_application_of symbol (term : Logic.term) =
  match term with
  | Apply (applied, _) when applied = symbol -> true
  | Forall (_, _, body) | Exists (_, body) -> has_application_of symbol body
  | _ -> List.exists (has_application_of symbol) (Logic.list_arguments term)

let find_definition (application : application) (term : Logic.term) =
  let defines body = not (has_application_of application.symbol body) in
  match term with
  | Operation (Equal, [ left; right ]) when left = application.term && defines right -> Some right
  | Operation (Equal, [ left; right ]) when right = application.term && defines left -> Some left
  | _ -> None
