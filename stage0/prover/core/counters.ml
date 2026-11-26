exception Blocks_credited_potential of string list

type lambda_bound = Logic.term * Obligation.t list

type state = {
  mutable counters : Costs.counter list;
  mutable conditional_counters : Costs.counter list;
  mutable recursive_costs_assumed : int;
  mutable lambdas_assuming_recursive_costs : Logic.term list;
  mutable lambda_costs : ((Logic.term * Language.Metric.t) * lambda_bound) list;
  mutable lambda_bounds :
    (Logic.term * ((Language.Metric.t * Logic.term) list * Core.local list)) list;
  mutable lambda_captures : (Logic.term * Core.local list) list;
  mutable credited_holders : string list;
  mutable newly_blocked_holders : string list;
}

let state =
  Private_state.make_key (fun () ->
      {
        counters = [];
        conditional_counters = [];
        recursive_costs_assumed = 0;
        lambdas_assuming_recursive_costs = [];
        lambda_costs = [];
        lambda_bounds = [];
        lambda_captures = [];
        credited_holders = [];
        newly_blocked_holders = [];
      })

let read_state query = Query.read_state query state
let list_counters query = (read_state query).counters
let count_recursive_costs_assumed query = (read_state query).recursive_costs_assumed

let note_recursive_cost_assumed query =
  let state = read_state query in
  state.recursive_costs_assumed <- state.recursive_costs_assumed + 1

let run_counting : 'a. Query.t -> Costs.counter list -> (unit -> 'a) -> 'a =
 fun query counters run ->
  let state = read_state query in
  let enclosing = state.counters in
  state.counters <- counters;
  Fun.protect ~finally:(fun () -> state.counters <- enclosing) run

let find_lambda_captures query lambda = List.assoc_opt lambda (read_state query).lambda_captures

let assumes_recursive_costs query lambda =
  List.mem lambda (read_state query).lambdas_assuming_recursive_costs

let take_lambda_cost query lambda metric =
  let state = read_state query in
  let bound = List.assoc_opt (lambda, metric) state.lambda_costs in
  if Option.is_some bound then
    state.lambda_costs <- List.remove_assoc (lambda, metric) state.lambda_costs;
  bound

let lookup_spent (frame : State.frame) counter =
  match List.assoc_opt counter frame.spent with Some spent -> spent | None -> Costs.zero

let start (frame : State.frame) =
  {
    frame with
    spent = List.map (fun counter -> (counter, Costs.zero)) (read_state frame.query).counters;
  }

let read_condition (environment : State.environment) (query : Query.t) counter =
  if List.mem counter (read_state query).conditional_counters then environment.condition else []

let list_loop_counters (environment : State.environment) (query : Query.t) locals (body : Mir.body)
    =
  let counters = ref [] in
  let note (loop : Mir.loop) =
    List.iter
      (function
        | Mir.Cost cost -> (
            match
              Conditions.find_obligation_condition
                (Conditions.decide environment query ~substitution:Types.no_substitution
                   cost.holds_when)
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

let assign (query : Query.t) (sources : (Costs.counter * Types.condition) list) =
  let counters = deduplicate (List.map fst sources) in
  let state = read_state query in
  state.counters <- counters;
  state.conditional_counters <-
    List.filter (fun counter -> not (List.mem (counter, []) sources)) counters

let spend (frame : State.frame) (amount_of : Costs.counter -> Logic.term) =
  if (read_state frame.query).counters = [] then frame
  else
    {
      frame with
      State.spent =
        List.map
          (fun (counter, term) ->
            if List.mem counter (read_state frame.query).counters then
              (counter, Logic.add term (amount_of counter))
            else (counter, term))
          frame.spent;
    }

let declare_unknown_amount (frame : State.frame) (counter : Costs.counter) =
  let amount = Facts.declare_fresh frame "spent" Logic.Int in
  Facts.assume frame (Logic.less_equal (Costs.least_amount counter.resource) amount);
  amount

let make_potential_credit (query : Query.t) change =
  if Option.is_none (Query.find_argument_sorts query Costs.credit_symbol) then begin
    let is_credited = Logic.Symbol.Variable { label = "cost.is_credited"; numbers = [] }
    and saved = Logic.Symbol.Variable { label = "cost.saved"; numbers = [] } in
    Query.declare query (Logic.Constant (is_credited, Logic.Bool));
    Query.declare query (Logic.Function (Costs.credit_symbol, [ Logic.Int ], Logic.Int));
    let applied = Logic.Apply (Costs.credit_symbol, [ Logic.Symbol saved ]) in
    Query.add_fact query
      (Logic.forall ~trigger:[ applied ]
         ( [ (saved, Logic.Int) ],
           Logic.equal applied
             (Logic.ite (Logic.Symbol is_credited) (Logic.Symbol saved) Costs.zero) ))
  end;
  let sums, constant = Logic.linearize change in
  let credit part = Logic.Apply (Costs.credit_symbol, [ part ]) in
  Logic.add
    (Logic.combine_linear (List.map (fun (part, factor) -> (credit part, factor)) sums, Z.zero))
    (if Z.equal constant Z.zero then Costs.zero else credit (Logic.Integer constant))

let whole_values = "*"

let list_blocked_holders (environment : State.environment) (query : Query.t) =
  (read_state query).newly_blocked_holders @ environment.blocked_holders

let count_held_potential (environment : State.environment) (query : Query.t) ~holder change =
  if List.mem holder (list_blocked_holders environment query) then Logic.at_least_zero change
  else begin
    let state = read_state query in
    if change <> Costs.zero && not (List.mem holder state.credited_holders) then
      state.credited_holders <- holder :: state.credited_holders;
    change
  end

let count_declared_potential (environment : State.environment) (query : Query.t) ~(of_ : Types.ty)
    change =
  match Types.erase_views of_ with
  | Named { path; _ } -> count_held_potential environment query ~holder:(Path.show path) change
  | _ -> count_held_potential environment query ~holder:whole_values change

let count_whole_potential (environment : State.environment) (query : Query.t) change =
  count_held_potential environment query ~holder:whole_values change

let rec list_reached_types (environment : State.environment) ?(entered = []) (ty : Types.ty) =
  match Types.erase_views ty with
  | Named { path; arguments } when not (List.exists (Path.equal path) entered) ->
      Path.show path
      :: List.concat_map
           (list_reached_types environment ~entered:(path :: entered))
           (Mir.Call_edges.list_instance_field_types environment.lookups.interface ty
           @ List.filter_map (function Types.Type argument -> Some argument | _ -> None) arguments)
  | _ -> []

let block_saved_potential (environment : State.environment) (query : Query.t) (held : Types.ty list)
    =
  let state = read_state query in
  let blocked = list_blocked_holders environment query in
  match
    List.filter
      (fun holder -> not (List.mem holder blocked))
      (List.sort_uniq String.compare
         (match List.concat_map (list_reached_types environment) held with
         | [] -> []
         | reached -> whole_values :: reached))
  with
  | [] -> ()
  | reached ->
      if List.exists (fun holder -> List.mem holder state.credited_holders) reached then
        raise (Blocks_credited_potential (reached @ blocked));
      state.newly_blocked_holders <- reached @ state.newly_blocked_holders

let spend_operation (frame : State.frame) ~potential_change ~held ?(note = fun _ _ -> ())
    (charge_of : Costs.counter -> Costs.charge) =
  let change = Option.map Lazy.from_fun potential_change in
  spend frame (fun counter ->
      let ({ amount; counted } : Costs.charge) = charge_of counter in
      let find_change () =
        match Option.map Lazy.force change with
        | change -> change
        | exception Facts.Unsupported _ -> None
      in
      let amount =
        match (counted, counter.amortized) with
        | No_potential, false -> amount
        | (Potential_change | Potential_growth), true ->
            block_saved_potential frame.environment frame.query (held ());
            amount
        | No_potential, true -> (
            match find_change () with
            | Some change ->
                Logic.add amount (count_whole_potential frame.environment frame.query change)
            | None -> declare_unknown_amount frame counter)
        | Potential_change, false -> (
            match find_change () with
            | Some change -> Logic.subtract amount (make_potential_credit frame.query change)
            | None -> declare_unknown_amount frame counter)
        | Potential_growth, false -> (
            match find_change () with
            | Some change ->
                Logic.subtract amount
                  (make_potential_credit frame.query (Logic.at_least_zero change))
            | None -> amount)
      in
      note counter amount;
      amount)

let spend_quantifier (frame : State.frame) ~count ~mark ~bound ~(before : State.frame)
    ~(after : State.frame) =
  spend frame (fun counter ->
      let spent =
        match (List.assoc_opt counter before.spent, List.assoc_opt counter after.spent) with
        | Some start, Some total -> Costs.since ~start total
        | _ -> Costs.zero
      in
      if Query.mentions_fresh_since frame.query mark spent || Logic.mentions [ bound ] spent then
        declare_unknown_amount frame counter
      else
        match counter.counting with
        | Units ->
            Logic.add
              (Logic.multiply (Logic.at_least_zero count) (Logic.add spent (Logic.int 1)))
              (Logic.int 1)
        | At_most | Exactly ->
            if spent = Costs.zero then Costs.zero else declare_unknown_amount frame counter)

let enter_body (frame : State.frame) sources ~body =
  assign frame.query
    (sources
    @
    match body with
    | Some body -> list_loop_counters frame.environment frame.query frame.locals body
    | None -> []);
  start frame

let run_without_counters query read = run_counting query [] read

type lambda_counters = {
  promised : (Costs.counter * Types.cost_bound) list;
  operand_counters : (Language.Metric.t * Costs.counter) list;
  enclosing_counters : Costs.counter list;
  enclosing_conditional_counters : Costs.counter list;
  recursive_costs_mark : int;
}

let enter_lambda (inside : State.frame) (function_type : Types.function_type) (body : Mir.body) =
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
            (read_state inside.query).counters
        in
        if is_counted && Option.is_none (Costs.find_stated_operand function_type.costs metric) then
          Some (metric, counter)
        else None)
      Language.Metric.all
  in
  let enclosing_counters = (read_state inside.query).counters
  and enclosing_conditional_counters = (read_state inside.query).conditional_counters in
  assign inside.query
    (List.map
       (fun (_, (counter : Costs.counter)) ->
         let is_conditional =
           List.for_all
             (fun (enclosing : Costs.counter) ->
               enclosing.resource <> counter.resource
               || List.mem enclosing (read_state inside.query).conditional_counters)
             (read_state inside.query).counters
         in
         (counter, if is_conditional then inside.environment.condition else []))
       operand_counters
    @ List.map (fun (counter, _) -> (counter, [])) promised
    @ list_loop_counters inside.environment inside.query inside.locals body);
  ( {
      promised;
      operand_counters;
      enclosing_counters;
      enclosing_conditional_counters;
      recursive_costs_mark = (read_state inside.query).recursive_costs_assumed;
    },
    start inside )

let leave_lambda (query : Query.t) counters =
  let state = read_state query in
  state.counters <- counters.enclosing_counters;
  state.conditional_counters <- counters.enclosing_conditional_counters

let check_lambda_exits (query : Query.t) counters (exits : State.frame list) location ~type_ ~mark =
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
          Obligations.oblige exit_ location
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
    Query.list_facts_since query mark
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
                  Obligations.make_closed_obligation exit_ location
                    (Lambda_call_above_bound { metric })
                    (Logic.less_equal spent bound))
                (List.combine exits spent) ) ))
        (Costs.find_cost_bound ~varies:(Query.mentions_fresh_since query mark) ~facts most))
    counters.operand_counters

let list_bound_terms bounds = List.map (fun (metric, (bound, _)) -> (metric, bound)) bounds

let has_another_cost (query : Query.t) term ~captures ~bounds =
  match List.assoc_opt term (read_state query).lambda_bounds with
  | Some noted -> noted <> (list_bound_terms bounds, captures)
  | None -> false

let note_lambda (frame : State.frame) counters term ~captures ~bounds =
  let state = read_state frame.query in
  if frame.makes_obligations && not (List.mem_assoc term state.lambda_bounds) then
    state.lambda_bounds <- (term, (list_bound_terms bounds, captures)) :: state.lambda_bounds;
  state.lambda_captures <- (term, captures) :: state.lambda_captures;
  if state.recursive_costs_assumed > counters.recursive_costs_mark then
    state.lambdas_assuming_recursive_costs <- term :: state.lambdas_assuming_recursive_costs;
  state.lambda_costs <-
    List.map (fun (metric, bound) -> ((term, metric), bound)) bounds @ state.lambda_costs
