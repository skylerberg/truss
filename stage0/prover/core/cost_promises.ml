type promise = {
  counter : Costs.counter;
  clause : Mir.cost;
  written_in : State.source;
  inherited : bool;
}

type state = {
  mutable call_targets : (Logic.term * Core.local) list;
  mutable bounded_counters : Costs.counter list;
}

let state = Private_state.make_key (fun () -> { call_targets = []; bounded_counters = [] })

let find_call_target query target =
  List.assoc_opt target (Query.read_state query state).call_targets

let is_bounded query counter = List.mem counter (Query.read_state query state).bounded_counters

let list_promises (environment : State.environment) (query : Query.t) (source : State.source) locals
    (costs : Mir.cost list) ~inherited ~counts_provider_potential =
  List.filter_map
    (fun (cost : Mir.cost) ->
      match Costs.find_resource cost ~locals with
      | None ->
          Facts.raise_unsupported (Facts.locate_source environment source cost.origin) Calls_target
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
          let state = Query.read_state query state in
          (match (cost.resource, resource) with
          | Calls (Function_parameter local), Calls (Through term) ->
              state.call_targets <- (term, local) :: state.call_targets
          | _ -> ());
          if counter.counting = Units && not (List.mem counter state.bounded_counters) then
            state.bounded_counters <- counter :: state.bounded_counters;
          Some { counter; clause = cost; written_in = source; inherited })
    costs

let enter_definition (frame : State.frame) promises ~body =
  Counters.enter_body frame
    (List.map (fun promise -> (promise.counter, promise.clause.holds_when)) promises)
    ~body

let check_promise_amounts (start : State.frame) promises ~output =
  List.iter
    (fun promise ->
      if not promise.inherited then
        match promise.clause.bound with
        | Order_of amount | At_most amount | Exactly amount ->
            let at_return =
              match output with
              | Some output when Contracts.mentions_result amount ->
                  let _, returned = Facts.suppose start "returned" in
                  let result = Encoding.arrive returned "result" output in
                  Validity.assume_valid returned output result;
                  { returned with result = Some result }
              | Some _ | None -> start
            in
            Validity.check_defined at_return ~holds_when:promise.clause.holds_when amount)
    promises

let check_promise ?cited (frame : State.frame) promise ~(at : State.frame) ~location =
  let spent = Counters.lookup_spent frame promise.counter in
  let amount =
    match promise.clause.bound with
    | Order_of amount | At_most amount | Exactly amount ->
        snd (Validity.read_specification { at with makes_obligations = false } amount)
  in
  let goal =
    match promise.counter.counting with
    | Units -> Logic.less_equal spent (Costs.bound amount)
    | Exactly -> Logic.equal spent amount
    | At_most -> Logic.less_equal spent amount
  in
  let unstated =
    List.filter
      (fun unbounded ->
        not (List.mem unbounded (Counters.list_unbounded_method_costs frame.query amount)))
      (Counters.list_unbounded_method_costs frame.query spent)
  in
  let goal = if unstated = [] then goal else Logic.Boolean false in
  let counting : Catalog.Prover.counting =
    match promise.counter.counting with Units | At_most -> Upper_bound | Exactly -> Exact
  and clause = Facts.quote promise.written_in promise.clause.origin in
  Obligations.oblige ?cited frame location ~holds_when:promise.clause.holds_when
    ~can_be_required:(promise.counter.counting <> Units)
    (Cost_promise
       {
         unstated;
         promise =
           (if promise.inherited then
              Inherited_promise
                {
                  counting;
                  promiser = Contracts.find_promiser frame.environment.lookups promise.written_in;
                  clause;
                }
            else Own_promise { counting; clause });
       })
    goal
