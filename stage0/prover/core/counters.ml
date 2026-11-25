let make_state () : State.cost_state =
  {
    counters = [];
    conditional_counters = [];
    bounded_counters = [];
    recursive_costs_assumed = 0;
    lambdas_assuming_recursive_costs = [];
    lambda_costs = [];
    lambda_captures = [];
    call_targets = [];
    call_amounts = [];
    potentials = [];
    holds_potential = Tables.Type_table.create 16;
    buffers = Tables.Type_table.create 16;
  }

let lookup_spent (frame : State.frame) counter =
  match List.assoc_opt counter frame.spent with Some spent -> spent | None -> Costs.zero

let start (context : State.context) (frame : State.frame) =
  { frame with spent = List.map (fun counter -> (counter, Costs.zero)) context.cost.counters }

let read_condition (context : State.context) counter =
  if List.mem counter context.cost.conditional_counters then context.condition else []

let list_loop_counters context locals (body : Mir.body) =
  let counters = ref [] in
  let note (loop : Mir.loop) =
    List.iter
      (function
        | Mir.Cost cost -> (
            match
              Conditions.find_obligation_condition
                (Conditions.decide context ~substitution:Types.no_substitution cost.holds_when)
            with
            | None -> ()
            | Some condition -> (
                match Costs.find_resource cost ~locals with
                | Some resource ->
                    counters :=
                      ( {
                          Costs.resource;
                          counting = Costs.classify_counting cost;
                          amortized = false;
                        },
                        condition )
                      :: !counters
                | None -> Facts.raise_unsupported Whole_definition Calls_target))
        | Invariant _ | Decreases _ -> ())
      loop.clauses
  in
  let rec visit (block : Mir.block) =
    List.iter
      (fun (statement : Mir.statement) ->
        (match statement.kind with
        | While { loop; _ } | For { loop; _ } -> note loop
        | Basic _ | Choose _ | Assert_by_bit_vector _ | Fork _ | Provide _ | Resume _ | Yield _
        | Jump _ ->
            ());
        List.iter visit (Mir.list_nested_blocks statement))
      block.statements
  in
  visit body.code;
  List.rev !counters

let deduplicate counters =
  List.fold_left
    (fun distinct counter -> if List.mem counter distinct then distinct else distinct @ [ counter ])
    [] counters

let assign (context : State.context) (sources : (Costs.counter * Types.condition) list) =
  let counters = deduplicate (List.map fst sources) in
  context.cost.counters <- counters;
  context.cost.conditional_counters <-
    List.filter (fun counter -> not (List.mem (counter, []) sources)) counters

let spend (context : State.context) (frame : State.frame) (amount_of : Costs.counter -> Logic.term)
    =
  if context.cost.counters = [] then frame
  else
    {
      frame with
      State.spent =
        List.map
          (fun (counter, term) ->
            if List.mem counter context.cost.counters then
              (counter, Logic.plus term (amount_of counter))
            else (counter, term))
          frame.spent;
    }

let declare_unknown_amount context frame (counter : Costs.counter) =
  let amount = Facts.declare_fresh context frame "spent" Logic.Int in
  Facts.assume context frame (Logic.less_equal (Costs.least_amount counter.resource) amount);
  amount

let spend_operation context frame ~potential_change ?(note = fun _ _ -> ())
    (charge_of : Costs.counter -> Costs.charge) =
  let change = Option.map Lazy.from_fun potential_change in
  spend context frame (fun counter ->
      let ({ amount; counted } : Costs.charge) = charge_of counter in
      let find_change () =
        match Option.map Lazy.force change with
        | change -> change
        | exception Facts.Unsupported _ -> None
      in
      let amount =
        match (counted, counter.amortized) with
        | No_potential, false | (Potential_change | Potential_growth), true -> amount
        | No_potential, true -> (
            match find_change () with
            | Some change -> Logic.plus amount change
            | None -> declare_unknown_amount context frame counter)
        | Potential_change, false -> (
            match find_change () with Some change -> Logic.minus amount change | None -> amount)
        | Potential_growth, false -> (
            match find_change () with
            | Some change -> Logic.minus amount (Logic.at_least_zero change)
            | None -> amount)
      in
      note counter amount;
      amount)

let spend_quantifier context frame ~count ~fresh_mark ~bound ~(before : State.frame)
    ~(after : State.frame) =
  spend context frame (fun counter ->
      let spent =
        match (List.assoc_opt counter before.spent, List.assoc_opt counter after.spent) with
        | Some start, Some total -> Costs.since ~start total
        | _ -> Costs.zero
      in
      if Facts.mentions_fresh_after context fresh_mark spent || Logic.mentions [ bound ] spent then
        declare_unknown_amount context frame counter
      else
        match counter.counting with
        | Units ->
            Logic.plus
              (Logic.times (Logic.at_least_zero count) (Logic.plus spent (Logic.int 1)))
              (Logic.int 1)
        | At_most | Exactly ->
            if spent = Costs.zero then Costs.zero else declare_unknown_amount context frame counter)

type promise = {
  counter : Costs.counter;
  clause : Mir.cost;
  written_in : State.source;
  inherited : bool;
}

let list_promises (context : State.context) (source : State.source) locals (costs : Mir.cost list)
    ~inherited ~counts_provider_potential =
  List.filter_map
    (fun (cost : Mir.cost) ->
      match Costs.find_resource cost ~locals with
      | None -> Facts.raise_unsupported (Facts.locate context source cost.origin) Calls_target
      | Some resource ->
          let counting = Costs.classify_counting cost in
          let counter =
            {
              Costs.resource;
              counting;
              amortized =
                (cost.amortized
                || counts_provider_potential && counting = Units
                   && match resource with Metric _ -> true | Calls _ -> false);
            }
          in
          (match (cost.resource, resource) with
          | Calls (Function_parameter local), Calls (Through term) ->
              context.cost.call_targets <- (term, local) :: context.cost.call_targets
          | _ -> ());
          if counter.counting = Units && not (List.mem counter context.cost.bounded_counters) then
            context.cost.bounded_counters <- counter :: context.cost.bounded_counters;
          Some { counter; clause = cost; written_in = source; inherited })
    costs

let enter_definition context (frame : State.frame) promises ~body =
  assign context
    (List.map (fun promise -> (promise.counter, promise.clause.holds_when)) promises
    @ match body with Some body -> list_loop_counters context frame.locals body | None -> []);
  start context frame

let check_promise_amounts context (start : State.frame) promises ~output =
  List.iter
    (fun promise ->
      if not promise.inherited then
        match promise.clause.bound with
        | Order_of amount | At_most amount | Exactly amount ->
            let result =
              Option.map
                (fun output ->
                  let result = Facts.arrive context start "result" output in
                  Validity.assume_valid context start output result;
                  result)
                output
            in
            Validity.check_defined context { start with result }
              ~holds_when:promise.clause.holds_when amount)
    promises

let check_promise ?restated (context : State.context) (frame : State.frame) promise
    ~(at : State.frame) ~location =
  let spent = lookup_spent frame promise.counter in
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
  let counting : Catalog.Prover.counting =
    match promise.counter.counting with Units | At_most -> Upper_bound | Exactly -> Exact
  and clause = Facts.quote promise.written_in promise.clause.origin in
  Facts.oblige context frame location ~holds_when:promise.clause.holds_when
    ~can_be_required:(promise.counter.counting <> Units)
    (Cost_promise
       (match restated with
       | Some (for_type, name, trait, declared) ->
           Restated_promise { counting; for_type; name; clause; trait; declared }
       | None when promise.inherited ->
           Inherited_promise
             {
               counting;
               promiser = Contracts.find_promiser context.lookups promise.written_in;
               clause;
             }
       | None -> Own_promise { counting; clause }))
    goal

type lambda_counters = {
  promised : (Costs.counter * Types.cost_bound) list;
  operand_counters : (Language.Metric.t * Costs.counter) list;
  enclosing_counters : Costs.counter list;
  enclosing_conditional_counters : Costs.counter list;
  recursive_costs_mark : int;
}

let enter_lambda (context : State.context) (inside : State.frame)
    (function_type : Types.function_type) (body : Mir.body) =
  let promised =
    List.filter_map
      (fun (cost : Types.cost) ->
        let counting : Costs.counting =
          match cost.bound with
          | Order_of -> Units
          | No_more_than _ -> At_most
          | Exactly_cost _ -> Exactly
        in
        match cost.resource with
        | Metric metric ->
            let counter =
              { Costs.resource = Metric metric; counting; amortized = cost.amortized }
            in
            Some (counter, cost.bound)
        | Calls _ -> None)
      function_type.costs
  in
  let operand_counters =
    List.filter_map
      (fun metric ->
        let counter = Costs.make_operand_counter metric in
        let is_counted =
          List.exists
            (fun (enclosing : Costs.counter) -> enclosing.resource = counter.resource)
            context.cost.counters
        in
        if is_counted && Option.is_none (Costs.find_stated_operand function_type.costs metric) then
          Some (metric, counter)
        else None)
      Language.Metric.all
  in
  let enclosing_counters = context.cost.counters
  and enclosing_conditional_counters = context.cost.conditional_counters in
  assign context
    (List.map
       (fun (_, (counter : Costs.counter)) ->
         let is_conditional =
           List.for_all
             (fun (enclosing : Costs.counter) ->
               enclosing.resource <> counter.resource
               || List.mem enclosing context.cost.conditional_counters)
             context.cost.counters
         in
         (counter, if is_conditional then context.condition else []))
       operand_counters
    @ List.map (fun (counter, _) -> (counter, [])) promised
    @ list_loop_counters context inside.locals body);
  ( {
      promised;
      operand_counters;
      enclosing_counters;
      enclosing_conditional_counters;
      recursive_costs_mark = context.cost.recursive_costs_assumed;
    },
    start context inside )

let leave_lambda (context : State.context) counters =
  context.cost.counters <- counters.enclosing_counters;
  context.cost.conditional_counters <- counters.enclosing_conditional_counters

let check_lambda_exits context counters (exits : State.frame list) location ~type_ ~fresh_mark
    ~facts_mark =
  List.iter
    (fun (exit_ : State.frame) ->
      List.iter
        (fun ((counter : Costs.counter), (bound : Types.cost_bound)) ->
          let spent = lookup_spent exit_ counter in
          let goal =
            match bound with
            | Order_of -> Logic.less_equal spent (Costs.bound (Logic.int 1))
            | No_more_than limit -> Logic.less_equal spent (Logic.Integer limit)
            | Exactly_cost limit -> Logic.equal spent (Logic.Integer limit)
          in
          Facts.oblige context exit_ location
            (Lambda_cost
               {
                 counting =
                   (match counter.counting with Units | At_most -> Upper_bound | Exactly -> Exact);
                 type_;
               })
            goal)
        counters.promised)
    exits;
  let facts =
    Fact_list.list_newest_since context.facts ~count:facts_mark
    @ List.map (fun (exit_ : State.frame) -> exit_.condition) exits
  in
  List.filter_map
    (fun ((metric : Language.Metric.t), counter) ->
      let spent = List.map (fun exit_ -> lookup_spent exit_ counter) exits in
      let most =
        match spent with
        | [] -> Costs.zero
        | first :: rest -> List.fold_left Logic.larger first rest
      in
      Option.map
        (fun bound ->
          ( metric,
            ( bound,
              List.filter_map
                (fun ((exit_ : State.frame), spent) ->
                  Facts.make_closed_obligation context exit_ location
                    (Lambda_call_above_bound { metric })
                    (Logic.less_equal spent bound))
                (List.combine exits spent) ) ))
        (Costs.find_cost_bound ~varies:(Facts.mentions_fresh_after context fresh_mark) ~facts most))
    counters.operand_counters

let note_lambda (context : State.context) counters term ~captures ~bounds =
  context.cost.lambda_captures <- (term, captures) :: context.cost.lambda_captures;
  if context.cost.recursive_costs_assumed > counters.recursive_costs_mark then
    context.cost.lambdas_assuming_recursive_costs <-
      term :: context.cost.lambdas_assuming_recursive_costs;
  context.cost.lambda_costs <-
    List.map (fun (metric, bound) -> ((term, metric), bound)) bounds @ context.cost.lambda_costs
