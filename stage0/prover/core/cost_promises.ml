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
      | None ->
          Facts.raise_unsupported
            (Facts.locate_source context.environment source cost.origin)
            Calls_target
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

let enter_definition (context : State.context) frame promises ~body =
  Counters.enter_body context frame
    (List.map (fun promise -> (promise.counter, promise.clause.holds_when)) promises)
    ~body

let check_promise_amounts (context : State.context) (start : State.frame) promises ~output =
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
                  Validity.assume_valid context returned output result;
                  { returned with result = Some result }
              | Some _ | None -> start
            in
            Validity.check_defined context at_return ~holds_when:promise.clause.holds_when amount)
    promises

let check_promise ?restated ?cited (context : State.context) (frame : State.frame) promise
    ~(at : State.frame) ~location =
  let spent = Counters.lookup_spent frame promise.counter in
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
  Obligations.oblige ?cited context frame location ~holds_when:promise.clause.holds_when
    ~can_be_required:(promise.counter.counting <> Units)
    (Cost_promise
       (match restated with
       | Some (for_type, name, trait, declared) ->
           Restated_promise { counting; for_type; name; clause; trait; declared }
       | None when promise.inherited ->
           Inherited_promise
             {
               counting;
               promiser = Contracts.find_promiser context.environment.lookups promise.written_in;
               clause;
             }
       | None -> Own_promise { counting; clause }))
    goal
