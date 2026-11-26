exception Blocks_credited_potential of string list

let make_state ?(blocked_holders = []) () : State.cost_state =
  {
    counters = [];
    conditional_counters = [];
    bounded_counters = [];
    recursive_costs_assumed = 0;
    lambdas_assuming_recursive_costs = [];
    lambda_costs = [];
    lambda_bounds = [];
    lambda_captures = [];
    call_targets = [];
    call_amounts = [];
    potentials = [];
    credited_holders = [];
    blocked_holders;
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
              (counter, Logic.add term (amount_of counter))
            else (counter, term))
          frame.spent;
    }

let declare_unknown_amount context frame (counter : Costs.counter) =
  let amount = Facts.declare_fresh context frame "spent" Logic.Int in
  Facts.assume context frame (Logic.less_equal (Costs.least_amount counter.resource) amount);
  amount

let make_potential_credit (context : State.context) change =
  if Option.is_none (Facts.find_argument_sorts context Costs.credit_symbol) then begin
    let is_credited = Logic.Symbol.Variable { label = "cost.is_credited"; numbers = [] }
    and saved = Logic.Symbol.Variable { label = "cost.saved"; numbers = [] } in
    Facts.declare context (Logic.Constant (is_credited, Logic.Bool));
    Facts.declare context (Logic.Function (Costs.credit_symbol, [ Logic.Int ], Logic.Int));
    let applied = Logic.Apply (Costs.credit_symbol, [ Logic.Symbol saved ]) in
    Facts.add_fact context
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

let count_held_potential (context : State.context) ~holder change =
  if List.mem holder context.cost.blocked_holders then Logic.at_least_zero change
  else begin
    if change <> Costs.zero && not (List.mem holder context.cost.credited_holders) then
      context.cost.credited_holders <- holder :: context.cost.credited_holders;
    change
  end

let count_declared_potential context ~(of_ : Types.ty) change =
  match Types.erase_views of_ with
  | Named { path; _ } -> count_held_potential context ~holder:(Path.show path) change
  | _ -> count_held_potential context ~holder:whole_values change

let count_whole_potential context change = count_held_potential context ~holder:whole_values change

let rec list_reached_types (context : State.context) ?(entered = []) (ty : Types.ty) =
  match Types.erase_views ty with
  | Named { path; arguments } when not (List.exists (Path.equal path) entered) ->
      Path.show path
      :: List.concat_map
           (list_reached_types context ~entered:(path :: entered))
           (Mir.Call_edges.list_instance_field_types context.lookups.interface ty
           @ List.filter_map (function Types.Type argument -> Some argument | _ -> None) arguments)
  | _ -> []

let block_saved_potential (context : State.context) (held : Types.ty list) =
  let blocked = context.cost.blocked_holders in
  match
    List.filter
      (fun holder -> not (List.mem holder blocked))
      (List.sort_uniq String.compare
         (match List.concat_map (list_reached_types context) held with
         | [] -> []
         | reached -> whole_values :: reached))
  with
  | [] -> ()
  | reached ->
      if List.exists (fun holder -> List.mem holder context.cost.credited_holders) reached then
        raise (Blocks_credited_potential (reached @ blocked));
      context.cost.blocked_holders <- reached @ blocked

let spend_operation context frame ~potential_change ~held ?(note = fun _ _ -> ())
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
        | No_potential, false -> amount
        | (Potential_change | Potential_growth), true ->
            block_saved_potential context (held ());
            amount
        | No_potential, true -> (
            match find_change () with
            | Some change -> Logic.add amount (count_whole_potential context change)
            | None -> declare_unknown_amount context frame counter)
        | Potential_change, false -> (
            match find_change () with
            | Some change -> Logic.subtract amount (make_potential_credit context change)
            | None -> declare_unknown_amount context frame counter)
        | Potential_growth, false -> (
            match find_change () with
            | Some change ->
                Logic.subtract amount (make_potential_credit context (Logic.at_least_zero change))
            | None -> amount)
      in
      note counter amount;
      amount)

let spend_quantifier context frame ~count ~mark ~bound ~(before : State.frame)
    ~(after : State.frame) =
  spend context frame (fun counter ->
      let spent =
        match (List.assoc_opt counter before.spent, List.assoc_opt counter after.spent) with
        | Some start, Some total -> Costs.since ~start total
        | _ -> Costs.zero
      in
      if Facts.mentions_fresh_since context mark spent || Logic.mentions [ bound ] spent then
        declare_unknown_amount context frame counter
      else
        match counter.counting with
        | Units ->
            Logic.add
              (Logic.multiply (Logic.at_least_zero count) (Logic.add spent (Logic.int 1)))
              (Logic.int 1)
        | At_most | Exactly ->
            if spent = Costs.zero then Costs.zero else declare_unknown_amount context frame counter)

let enter_body context (frame : State.frame) sources ~body =
  assign context
    (sources
    @ match body with Some body -> list_loop_counters context frame.locals body | None -> []);
  start context frame

let run_without_counters : 'a. _ -> (unit -> 'a) -> 'a =
 fun (context : State.context) read ->
  let saved = context.cost.counters in
  context.cost.counters <- [];
  Fun.protect ~finally:(fun () -> context.cost.counters <- saved) read

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

let check_lambda_exits context counters (exits : State.frame list) location ~type_ ~mark =
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
          Obligations.oblige context exit_ location
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
    Query.list_facts_since context.query mark
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
                  Obligations.make_closed_obligation context exit_ location
                    (Lambda_call_above_bound { metric })
                    (Logic.less_equal spent bound))
                (List.combine exits spent) ) ))
        (Costs.find_cost_bound ~varies:(Facts.mentions_fresh_since context mark) ~facts most))
    counters.operand_counters

let list_bound_terms bounds = List.map (fun (metric, (bound, _)) -> (metric, bound)) bounds

let has_another_cost (context : State.context) term ~captures ~bounds =
  match List.assoc_opt term context.cost.lambda_bounds with
  | Some noted -> noted <> (list_bound_terms bounds, captures)
  | None -> false

let note_lambda (context : State.context) (frame : State.frame) counters term ~captures ~bounds =
  if frame.makes_obligations && not (List.mem_assoc term context.cost.lambda_bounds) then
    context.cost.lambda_bounds <-
      (term, (list_bound_terms bounds, captures)) :: context.cost.lambda_bounds;
  context.cost.lambda_captures <- (term, captures) :: context.cost.lambda_captures;
  if context.cost.recursive_costs_assumed > counters.recursive_costs_mark then
    context.cost.lambdas_assuming_recursive_costs <-
      term :: context.cost.lambdas_assuming_recursive_costs;
  context.cost.lambda_costs <-
    List.map (fun (metric, bound) -> ((term, metric), bound)) bounds @ context.cost.lambda_costs
