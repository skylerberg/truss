module Axiom_clause_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Logic.symbol * Resolve.Names.key * Path.t * Core.origin
end))

type open_axiom = {
  parameters : Logic.symbol list;
  mutable typing_facts : Logic.term list;
  mutable can_call_facts : Logic.term list;
  mutable is_read_at_calls : bool;
}

type state = {
  mutable axiomatizing : Logic.symbol list;
  mutable open_axioms : open_axiom list;
  axiom_clauses : unit Axiom_clause_table.t;
  needs_can_call : unit Tables.Symbol_table.t;
}

let axiom_state =
  Private_state.make_key (fun () ->
      {
        axiomatizing = [];
        open_axioms = [];
        axiom_clauses = Axiom_clause_table.create 16;
        needs_can_call = Tables.Symbol_table.create 16;
      })

let read_state query = Query.read_state query axiom_state

let find_innermost_axiom (frame : State.frame) term =
  match (read_state frame.query).open_axioms with
  | axiom :: _
    when let named = List.filter (fun name -> Logic.mentions [ name ] term) frame.bound in
         named <> [] && List.for_all (fun name -> List.mem name axiom.parameters) named ->
      Some axiom
  | _ -> None

let is_typing_fact (frame : State.frame) term =
  Option.is_some (find_innermost_axiom frame (Logic.( ==> ) frame.condition term))

let assume_typed (frame : State.frame) term =
  let guarded = Logic.( ==> ) frame.condition term in
  match find_innermost_axiom frame guarded with
  | Some axiom -> axiom.typing_facts <- guarded :: axiom.typing_facts
  | None -> Facts.assume frame term

let assume_can_call_fact (frame : State.frame) term =
  let guarded = Logic.( ==> ) frame.condition term in
  match find_innermost_axiom frame guarded with
  | Some axiom -> axiom.can_call_facts <- guarded :: axiom.can_call_facts
  | None -> Facts.assume frame term

let assume_ground_facts (frame : State.frame) value list_facts =
  if not (Logic.mentions frame.bound value) then List.iter (Facts.assume frame) (list_facts ())
  else Option.iter (fun axiom -> axiom.is_read_at_calls <- true) (find_innermost_axiom frame value)

type application = {
  symbol : Logic.symbol;
  sorts : Logic.sort list;
  term : Logic.term;
  is_limited : bool;
}

let declare_function query ~path ~type_arguments ~sorts ~result_type =
  let symbol = Logic.Symbol.Function { callee = path; type_arguments } in
  let result_sort = Encoding.sort_of result_type in
  (match Signatures.find_signature symbol with
  | None -> Query.declare query (Logic.Function (symbol, sorts, result_sort))
  | Some derived ->
      if derived <> (sorts, result_sort) then
        Facts.raise_bug "the call of `%s` has another signature than the one derived for it"
          (Path.show path));
  symbol

let apply_can_call query (application : application) arguments =
  let symbol =
    match application.symbol with
    | Logic.Symbol.Function { callee; type_arguments } | Limited { callee; type_arguments } ->
        Logic.Symbol.Can_call { callee; type_arguments }
    | symbol -> Facts.raise_bug "`%s` is applied as a function" (Logic.show_term (Symbol symbol))
  in
  Query.declare query (Logic.Function (symbol, application.sorts, Logic.Bool));
  Logic.Apply (symbol, arguments)

let make_numbered_parameters label sorts =
  List.mapi (fun index sort -> (Logic.Symbol.Variable { label; numbers = [ index ] }, sort)) sorts

let apply (frame : State.frame) ~path ~type_arguments ~sorts ~result_type ~arguments
    ~is_on_bound_values =
  let function_symbol = Logic.Symbol.Function { callee = path; type_arguments } in
  let is_limited = List.mem function_symbol (read_state frame.query).axiomatizing in
  let symbol =
    if is_limited then begin
      let limited = Logic.Symbol.Limited { callee = path; type_arguments } in
      Query.declare frame.query (Logic.Function (limited, sorts, Encoding.sort_of result_type));
      Query.run_once frame.query (Limited_link function_symbol) (fun () ->
          let parameters = make_numbered_parameters "linked" sorts in
          let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
          let applied = Logic.Apply (function_symbol, inputs) in
          Query.add_theorem frame.query ~because:(Defines (Logic.Symbol limited))
            (Logic.forall ~trigger:[ applied ]
               (parameters, Logic.equal applied (Logic.Apply (limited, inputs)))));
      limited
    end
    else function_symbol
  in
  let term = Logic.Apply (symbol, arguments) in
  Facts.assume frame (Encoding.make_in_range result_type term);
  if Encoding.find_bounds result_type <> None && is_on_bound_values then
    Query.run_once frame.query (In_range symbol) (fun () ->
        let parameters = make_numbered_parameters "ranged" sorts in
        Query.add_theorem frame.query ~because:(Proven_by path)
          (Logic.forall
             ( parameters,
               Encoding.make_in_range result_type
                 (Logic.Apply (symbol, List.map (fun (name, _) -> Logic.Symbol name) parameters)) )));
  { symbol; sorts; term; is_limited }

let rec strip_binder_conditions names condition =
  if not (Logic.mentions names condition) then condition
  else
    match condition with
    | Logic.Operation (And, [ outer; _ ]) -> strip_binder_conditions names outer
    | _ -> Logic.Boolean true

let list_binders_reached (frame : State.frame) term =
  let is_reached reached (name, _, _) =
    Logic.mentions [ name ] term
    || List.exists (fun (_, _, premise) -> Logic.mentions [ name ] premise) reached
  in
  let rec grow reached =
    match
      List.filter
        (fun binder -> (not (List.memq binder reached)) && is_reached reached binder)
        frame.binders
    with
    | [] -> reached
    | added -> grow (reached @ added)
  in
  let reached = grow [] in
  List.filter (fun binder -> List.memq binder reached) (List.rev frame.binders)

let assume_can_call (frame : State.frame) (application : application) ~arguments =
  if Tables.Symbol_table.mem (read_state frame.query).needs_can_call application.symbol then
    let can_call = apply_can_call frame.query application arguments in
    let outside =
      {
        frame with
        condition =
          strip_binder_conditions
            (List.map (fun (name, _, _) -> name) frame.binders)
            frame.condition;
      }
    in
    match list_binders_reached frame can_call with
    | [] -> assume_can_call_fact outside can_call
    | outermost_first ->
        let closed =
          List.mapi
            (fun index (name, sort, _) ->
              (name, (Logic.Symbol.Variable { label = "closed"; numbers = [ index ] }, sort)))
            outermost_first
        in
        let rename =
          Logic.substitute
            (List.map (fun (name, (variable, _)) -> (name, Logic.Symbol variable)) closed)
        in
        let variables = List.map snd closed in
        let can_call = rename can_call and applied = rename application.term in
        let covers term =
          Logic.is_matchable term
          && List.for_all (fun (name, _) -> Logic.mentions [ name ] term) variables
        in
        let trigger =
          if Query.is_defined frame.query application.symbol then can_call else applied
        in
        if covers trigger then
          assume_can_call_fact outside
            (Logic.forall ~trigger:[ trigger ]
               ( variables,
                 Logic.( ==> )
                   (Logic.conjunction
                      (List.map (fun (_, _, premise) -> rename premise) outermost_first))
                   can_call ));
        Facts.assume frame (apply_can_call frame.query application arguments)

let make_fresh_parameters (query : Query.t) label sorts =
  let axiom = Query.take_fresh_number query in
  List.mapi
    (fun index sort -> (Logic.Symbol.Variable { label; numbers = [ axiom; index ] }, sort))
    sorts

let find_readable_clause (query : Query.t) mark clause inside =
  match snd (Validity.read_specification inside clause) with
  | term when not (Query.mentions_fresh_since query mark term) -> Some term
  | _ -> None
  | exception Facts.Unsupported _ -> None

let axiomatize (query : Query.t) symbol parameters make =
  let mark = Query.mark query in
  let axiom =
    {
      parameters = List.map fst parameters;
      typing_facts = [];
      can_call_facts = [];
      is_read_at_calls = false;
    }
  in
  let state = read_state query in
  let axiomatizing = state.axiomatizing and open_axioms = state.open_axioms in
  state.axiomatizing <- symbol :: axiomatizing;
  state.open_axioms <- axiom :: open_axioms;
  Fun.protect
    ~finally:(fun () ->
      state.axiomatizing <- axiomatizing;
      state.open_axioms <- open_axioms)
    (fun () ->
      let stated, newest_facts =
        Query.run_in_scope query (List.map fst parameters) (fun () -> make axiom)
      in
      let list_stated_once newest_first =
        let stated = Tables.Term_table.create 16 in
        List.filter
          (fun term ->
            if Query.mentions_fresh_since query mark term || Tables.Term_table.mem stated term then
              false
            else begin
              Tables.Term_table.replace stated term ();
              true
            end)
          (List.rev newest_first)
      in
      ( stated,
        list_stated_once newest_facts,
        list_stated_once axiom.typing_facts,
        list_stated_once axiom.can_call_facts ))

let find_smaller_than_entry (frame : State.frame) (callee_clauses : State.clauses) ~group_member
    ~callee_entry ~inputs =
  match group_member with
  | None -> Some (Logic.Boolean true)
  | Some member ->
      Termination.find_induction_premise frame callee_clauses ~callee:member ~callee_entry
        ~argument_at:(List.nth inputs)

let state_with_trigger (outer : State.frame) (application : application) (contract : State.contract)
    ~substitution_of ~result_type ~group_member ~is_triggered =
  let symbol = application.symbol and sorts = application.sorts in
  let callee_clauses = contract.callee_clauses
  and precondition = Contracts.select_precondition_clauses contract in
  Query.run_once outer.query (Contract_of symbol) (fun () ->
      let parameters = make_fresh_parameters outer.query "ensured" sorts in
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
        Contracts.make_entry_frame outside clauses ~arguments
          ~substitution:(substitution_of clauses)
      in
      let mark = Query.mark outer.query in
      let stated, facts, typing_facts, can_call_facts =
        axiomatize outer.query symbol parameters (fun axiom ->
            let valid_arguments =
              Logic.conjunction
                (List.map2
                   (fun (parameter : Mir.parameter) input ->
                     let ty =
                       Types.substitute_erased (substitution_of callee_clauses) parameter.type_
                     in
                     Validity.make_validity outside ~assuming:true ~includes_ranges:true ty input)
                   callee_clauses.parameters inputs)
            in
            let smaller =
              find_smaller_than_entry outside callee_clauses ~group_member
                ~callee_entry:(bind callee_clauses) ~inputs
            in
            let readable_clauses =
              List.filter_map
                (fun (clauses : State.clauses) ->
                  let inside =
                    { (bind clauses) with result = Some applied; makes_obligations = false }
                  in
                  let read_required (stated_by : State.clauses) requirements =
                    List.map
                      (fun requirement ->
                        find_readable_clause outer.query mark requirement (bind stated_by))
                      (Facts.list_clauses requirements)
                  in
                  let required =
                    read_required precondition precondition.requires
                    @ read_required callee_clauses callee_clauses.panics_unless
                  in
                  if List.mem None required then None
                  else
                    let read_ensures (clause : Mir.formula) =
                      axiom.is_read_at_calls <- false;
                      Option.map
                        (fun term -> (clause, term, axiom.is_read_at_calls))
                        (find_readable_clause outer.query mark clause inside)
                    in
                    match List.filter_map read_ensures clauses.ensures with
                    | [] -> None
                    | ensures -> Some (clauses, List.filter_map Fun.id required, ensures))
                (Contracts.list_clause_sets contract)
            in
            match smaller with
            | Some smaller
              when readable_clauses <> []
                   && not
                        (Query.mentions_fresh_since outer.query mark
                           (Logic.( &&& ) valid_arguments smaller)) ->
                Some (valid_arguments, smaller, readable_clauses)
            | Some _ | None -> None)
      in
      match stated with
      | None -> ()
      | Some (valid_arguments, smaller, readable_clauses) -> (
          let typed_arguments =
            Logic.( &&& ) valid_arguments (Logic.nest_under_conditions typing_facts)
          in
          let proven_by = callee_clauses.callee.definition in
          let premise, state_consequences_of_can_call =
            if typed_arguments = Logic.Boolean true then (smaller, fun _ -> ())
            else begin
              let can_call = apply_can_call outer.query application inputs in
              let state_about_can_call fact =
                Query.add_theorem outer.query ~because:(Proven_by proven_by)
                  (Logic.forall ~trigger:[ can_call ] (parameters, fact))
              in
              Tables.Symbol_table.replace (read_state outer.query).needs_can_call symbol ();
              state_about_can_call (Logic.( ==> ) typed_arguments can_call);
              ( Logic.( &&& ) can_call smaller,
                fun consequences ->
                  if consequences <> [] then
                    state_about_can_call
                      (Logic.( ==> ) can_call (Logic.nest_under_conditions consequences)) )
            end
          in
          let definition =
            match (is_triggered, facts, readable_clauses) with
            | true, [], [ (_, required, [ (_, Logic.Operation (Equal, [ left; right ]), _) ]) ] -> (
                let defined_by body =
                  if
                    Logic.mentions [ symbol ] body
                    || Encoding.find_bounds result_type <> None
                    || not (Logic.has_quantifier body)
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
                  (fun ((clause : Mir.formula), _, is_read_at_calls) ->
                    if not is_read_at_calls then
                      Axiom_clause_table.replace (read_state outer.query).axiom_clauses
                        (symbol, clauses.callee.key, clauses.callee.definition, clause.origin)
                        ())
                  ensures)
              readable_clauses;
          match definition with
          | Some (required, body) ->
              let unspecified = Logic.Symbol.Unspecified symbol
              and result_sort = Encoding.sort_of result_type in
              Query.declare outer.query (Logic.Function (unspecified, sorts, result_sort));
              Query.declare outer.query
                (Logic.Definition
                   {
                     symbol;
                     parameters;
                     result = result_sort;
                     body =
                       Logic.ite
                         (Logic.conjunction (premise :: required))
                         body
                         (Logic.Apply (unspecified, inputs));
                   });
              state_consequences_of_can_call (typing_facts @ can_call_facts)
          | None ->
              state_consequences_of_can_call typing_facts;
              Query.add_theorem outer.query ~because:(Proven_by proven_by)
                (Logic.forall
                   ~trigger:(if is_triggered then [ applied ] else [])
                   ( parameters,
                     Logic.( ==> ) premise
                       (Logic.conjunction
                          (Logic.nest_under_conditions (can_call_facts @ facts)
                          :: List.map
                               (fun (_, required, ensures) ->
                                 Logic.( ==> ) (Logic.conjunction required)
                                   (Logic.conjunction (List.map (fun (_, term, _) -> term) ensures)))
                               readable_clauses)) ))))

let state outer (application : application) (contract : State.contract) ~substitution_of
    ~result_type ~group_member ~is_on_bound_values =
  let add =
    state_with_trigger outer application contract ~substitution_of ~result_type ~group_member
  in
  if not application.is_limited then
    if contract.result_kind = `Returns && not (Types.equal result_type Types.unit) then
      add ~is_triggered:true
    else if is_on_bound_values then add ~is_triggered:false

let states (query : Query.t) (application : application) (clauses : State.clauses)
    (clause : Mir.formula) =
  Axiom_clause_table.mem (read_state query).axiom_clauses
    (application.symbol, clauses.callee.key, clauses.callee.definition, clause.origin)

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
