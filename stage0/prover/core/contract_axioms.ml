module Axiom_clause_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Logic.symbol * Resolve.Names.key * Path.t * Core.origin
end))

type open_axiom = {
  parameters : Logic.symbol list;
  mutable hypotheses : Logic.term list;
  mutable at_calls : (State.frame -> (Logic.term -> Logic.term) -> unit) list;
}

type state = {
  mutable axiomatizing : Logic.symbol list;
  mutable open_axioms : open_axiom list;
  axioms_of : open_axiom Tables.Symbol_table.t;
  axiom_clauses : unit Axiom_clause_table.t;
}

let axiom_state =
  Private_state.make_key (fun () ->
      {
        axiomatizing = [];
        open_axioms = [];
        axioms_of = Tables.Symbol_table.create 16;
        axiom_clauses = Axiom_clause_table.create 16;
      })

let read_state query = Query.read_state query axiom_state

let find_innermost_axiom (frame : State.frame) term =
  match (read_state frame.query).open_axioms with
  | axiom :: _
    when let named = List.filter (fun name -> Logic.mentions [ name ] term) frame.bound in
         named <> [] && List.for_all (fun name -> List.mem name axiom.parameters) named ->
      Some axiom
  | _ -> None

let assume_typed (frame : State.frame) term =
  let guarded = Logic.( ==> ) frame.condition term in
  match find_innermost_axiom frame guarded with
  | Some axiom -> axiom.hypotheses <- guarded :: axiom.hypotheses
  | None -> Facts.assume frame term

let rec map_each_value (frame : State.frame) value make =
  if not (Logic.mentions frame.bound value) then make frame value
  else
    match find_innermost_axiom frame value with
    | Some axiom ->
        axiom.at_calls <-
          (fun frame substitute -> map_each_value frame (substitute value) make) :: axiom.at_calls
    | None -> ()

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

let run_limiting (query : Query.t) symbols run =
  let state = read_state query in
  let axiomatizing = state.axiomatizing in
  state.axiomatizing <- symbols @ axiomatizing;
  Fun.protect ~finally:(fun () -> state.axiomatizing <- axiomatizing) run

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
  let axiom = { parameters = List.map fst parameters; hypotheses = []; at_calls = [] } in
  let state = read_state query in
  let axiomatizing = state.axiomatizing and open_axioms = state.open_axioms in
  state.axiomatizing <- symbol :: axiomatizing;
  state.open_axioms <- axiom :: open_axioms;
  Fun.protect
    ~finally:(fun () ->
      state.axiomatizing <- axiomatizing;
      state.open_axioms <- open_axioms)
    (fun () ->
      let stated, newest_facts = Query.run_in_scope query (List.map fst parameters) make in
      let drop_fresh_terms terms =
        List.filter (fun term -> not (Query.mentions_fresh_since query mark term)) (List.rev terms)
      in
      axiom.hypotheses <- drop_fresh_terms axiom.hypotheses;
      (stated, Logic.conjunction (drop_fresh_terms newest_facts), axiom))

let find_smaller_than_entry (frame : State.frame) (callee_clauses : State.clauses) ~group_member
    ~callee_entry ~inputs ~substitution =
  let through_recursion =
    match group_member with
    | None -> Some (Logic.Boolean true)
    | Some member ->
        Termination.find_induction_premise frame callee_clauses ~callee:member ~callee_entry
          ~argument_at:(List.nth inputs)
  in
  match
    ( through_recursion,
      Termination.find_law_induction_premise frame callee_clauses ~substitution ~inputs )
  with
  | Some through_recursion, Some through_laws -> Some (Logic.( &&& ) through_recursion through_laws)
  | None, _ | _, None -> None

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
      let stated, facts, axiom =
        axiomatize outer.query symbol parameters (fun () ->
            let valid =
              Logic.conjunction
                (List.map2
                   (fun (parameter : Mir.parameter) input ->
                     let ty =
                       Types.substitute_erased (substitution_of callee_clauses) parameter.type_
                     in
                     Logic.( &&& ) (Encoding.make_in_range ty input)
                       (Validity.make_validity outside ~assuming:true ty input))
                   callee_clauses.parameters inputs)
            in
            let smaller =
              find_smaller_than_entry outside callee_clauses ~group_member
                ~callee_entry:(bind callee_clauses) ~inputs
                ~substitution:(substitution_of callee_clauses)
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
                    match
                      List.filter_map
                        (fun (clause : Mir.formula) ->
                          Option.map
                            (fun term -> (clause, term))
                            (find_readable_clause outer.query mark clause inside))
                        clauses.ensures
                    with
                    | [] -> None
                    | ensures -> Some (clauses, List.filter_map Fun.id required, ensures))
                (Contracts.list_clause_sets contract)
            in
            match smaller with
            | Some smaller ->
                let premise = Logic.( &&& ) valid smaller in
                if readable_clauses = [] || Query.mentions_fresh_since outer.query mark premise then
                  None
                else Some (premise, readable_clauses)
            | None -> None)
      in
      match stated with
      | None -> ()
      | Some (premise, readable_clauses) -> (
          let has_quantifier_through_definitions body =
            Logic.has_quantifier body
            || Logic.mentions (Query.list_defined_symbols outer.query) body
          in
          let definition =
            match (is_triggered, facts, readable_clauses) with
            | ( true,
                Logic.Boolean true,
                [ (_, required, [ (_, Logic.Operation (Equal, [ left; right ])) ]) ] ) -> (
                let defined_by body =
                  if
                    Logic.mentions [ symbol ] body
                    || Encoding.find_bounds result_type <> None
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
                    Axiom_clause_table.replace (read_state outer.query).axiom_clauses
                      (symbol, clauses.callee.key, clauses.callee.definition, clause.origin)
                      ())
                  ensures)
              readable_clauses;
          Tables.Symbol_table.add (read_state outer.query).axioms_of symbol axiom;
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
                         (Logic.conjunction ((premise :: axiom.hypotheses) @ required))
                         body
                         (Logic.Apply (unspecified, inputs));
                   })
          | None ->
              Query.add_theorem outer.query ~because:(Proven_by callee_clauses.callee.definition)
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

let assume_hypotheses (frame : State.frame) (application : application) ~arguments =
  if not application.is_limited then
    List.iter
      (fun axiom ->
        let substitute = Logic.substitute (List.combine axiom.parameters arguments) in
        List.iter (fun hypothesis -> assume_typed frame (substitute hypothesis)) axiom.hypotheses;
        List.iter (fun apply_hook -> apply_hook frame substitute) axiom.at_calls)
      (Tables.Symbol_table.find_all (read_state frame.query).axioms_of application.symbol)

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
