type gain = No_gain | Whole_potential | Potential_without_elements | Whole_potential_deducted
type one_iteration_bound = { spent_at_head : Logic.term; bound : Logic.term }

type rule =
  | Clause_bound of { written : Mir.cost; gained_at_head : Logic.term option; mutable gain : gain }
  | Per_iteration of {
      rules : (gain * Logic.term) list;
      mutable one_iteration_bound : one_iteration_bound option;
    }

type loop_cost = {
  counter : Costs.counter;
  entry : Logic.term;
  rule : rule;
  measure_gained : gain -> State.frame -> Logic.term;
  holds_when : Types.condition;
}

type t = {
  costs : loop_cost list;
  fresh_mark : int;
  facts_mark : int;
  recursive_costs_mark : int;
  changed : State.changed_part list;
}

let read_declared_part_type context (part : State.changed_part) =
  List.fold_left
    (fun declared field ->
      match
        Option.bind
          (Potentials.list_declared_fields context declared)
          (List.assoc_opt (None, field))
      with
      | Some field_type -> field_type
      | None ->
          Facts.raise_bug "a loop changes the field `%s`, which `%s` does not declare" field
            (Types.show declared))
    part.declared_root_type part.fields

let measure_held_gains context (entry : State.frame) (changed : State.changed_part list) =
  let held =
    List.filter_map
      (fun part ->
        Option.map
          (fun _ ->
            ( read_declared_part_type context part,
              fun (at : State.frame) -> Option.map snd (Validity.find_changed_part context at part)
            ))
          (Validity.find_changed_part context entry part))
      changed
  in
  let sum_held measure (at : State.frame) =
    List.fold_left
      (fun total (ty, read) ->
        match read at with Some term -> Logic.add total (measure at ty term) | None -> total)
      Costs.zero held
  in
  let measure_whole = sum_held (fun at ty term -> Potentials.compute_potential context at ty term)
  and measure_elements =
    sum_held (fun _ ty term -> Potentials.compute_elements_potential context ty term)
  in
  lazy
    (let holds_potential = List.exists (fun (ty, _) -> Potentials.has_potential context ty) held in
     let whole_on_entry = measure_whole entry in
     let elements_on_entry = measure_elements entry in
     let rec measure_gained gain (at : State.frame) =
       match gain with
       | No_gain -> Costs.zero
       | Whole_potential -> Logic.subtract (measure_whole at) whole_on_entry
       | Whole_potential_deducted -> Logic.subtract whole_on_entry (measure_whole at)
       | Potential_without_elements ->
           Logic.subtract
             (measure_gained Whole_potential at)
             (Logic.subtract (measure_elements at) elements_on_entry)
     in
     ( (if holds_potential then [ Whole_potential ] else [])
       @ (No_gain :: (if elements_on_entry = Costs.zero then [] else [ Potential_without_elements ])),
       measure_gained ))

let list_loop_costs context (frame : State.frame) (clauses : Mir.loop_clause list) ~held_gains =
  List.map
    (fun (counter : Costs.counter) ->
      let gains, measure_gained = Lazy.force held_gains in
      let gains =
        if counter.amortized then
          List.filter_map
            (function
              | Whole_potential -> Some Whole_potential_deducted
              | No_gain -> Some No_gain
              | Potential_without_elements | Whole_potential_deducted -> None)
            gains
        else gains
      in
      let entry = Counters.lookup_spent frame counter in
      let written =
        List.find_map
          (fun (clause : Mir.loop_clause) ->
            match clause with
            | Cost cost
              when Costs.is_same_resource cost ~locals:frame.locals counter
                   && Costs.classify_counting cost = counter.counting ->
                Some cost
            | _ -> None)
          clauses
      in
      let rule =
        match written with
        | Some written ->
            let gained_at_head =
              if List.mem Whole_potential gains && counter.counting <> Exactly then
                Some (Facts.declare_fresh context frame "gained" Logic.Int)
              else None
            in
            Clause_bound { written; gained_at_head; gain = No_gain }
        | None ->
            let needs_whole_potential = counter.counting = Exactly in
            Per_iteration
              {
                rules =
                  List.filter_map
                    (fun gain ->
                      if gain = Potential_without_elements && needs_whole_potential then None
                      else Some (gain, Facts.declare_fresh context frame "per" Logic.Int))
                    gains;
                one_iteration_bound = None;
              }
      in
      let is_conditional_clause =
        match written with
        | Some written ->
            Conditions.find_obligation_condition
              (Conditions.decide context ~substitution:Types.no_substitution written.holds_when)
            <> Some []
        | None -> false
      in
      let holds_when =
        if is_conditional_clause then context.condition else Counters.read_condition context counter
      in
      { counter; entry; rule; measure_gained; holds_when })
    context.cost.counters

let read_amount context (at : State.frame) (cost : Mir.cost) =
  match cost.bound with
  | Order_of amount | At_most amount | Exactly amount ->
      snd (Validity.read_specification context at amount)

let make_clause_bound (counter : Costs.counter) ~since ~amount =
  match counter.counting with
  | Units -> Logic.less_equal since (Costs.bound amount)
  | Exactly -> Logic.equal since amount
  | At_most -> Logic.less_equal since amount

let oblige_clause context (frame : State.frame) cost (written : Mir.cost) ~moment ~since =
  let amount = read_amount context frame written in
  Facts.oblige context frame
    (Facts.locate context frame.source written.origin)
    (Loop_cost_clause { clause = Facts.quote frame.source written.origin; moment })
    (make_clause_bound cost.counter ~since ~amount)

let make_count_bound ~(counter : Costs.counter) ~at ~bound =
  if counter.counting = Exactly then Logic.equal at bound else Logic.less_equal at bound

let check_entry context frame costs =
  List.iter
    (fun cost ->
      Conditions.with_obligation_condition context cost.holds_when @@ fun () ->
      match cost.rule with
      | Clause_bound { written; _ } ->
          oblige_clause context frame cost written ~moment:On_entry ~since:Costs.zero
      | Per_iteration _ -> ())
    costs

let enter (context : State.context) (frame : State.frame) ~entry clauses ~holds ~changed =
  let costs =
    list_loop_costs context frame clauses ~held_gains:(measure_held_gains context frame holds)
  in
  check_entry context entry costs;
  {
    costs;
    fresh_mark = context.fresh;
    facts_mark = Fact_list.count context.facts;
    recursive_costs_mark = context.cost.recursive_costs_assumed;
    changed;
  }

let declare_iterations context head loop =
  if
    List.exists
      (fun (cost : loop_cost) ->
        match cost.rule with Per_iteration _ -> true | Clause_bound _ -> false)
      loop.costs
  then begin
    let iterations = Facts.declare_fresh context head "iterations" Logic.Int in
    Facts.assume context head (Logic.less_equal (Logic.int 0) iterations);
    Some iterations
  end
  else None

let enter_head context head loop ~iterations =
  let iterations = Option.value iterations ~default:Costs.zero in
  let head =
    {
      head with
      State.spent =
        List.map
          (fun cost -> (cost.counter, Facts.declare_fresh context head "spent" Logic.Int))
          loop.costs;
    }
  in
  List.iter
    (fun cost ->
      let at_head = Counters.lookup_spent head cost.counter in
      match cost.rule with
      | Clause_bound { written; gained_at_head; _ } ->
          let since =
            Logic.add
              (Logic.subtract at_head cost.entry)
              (Option.value gained_at_head ~default:Costs.zero)
          in
          let amount = read_amount context { head with makes_obligations = false } written in
          Facts.assume context head (make_clause_bound cost.counter ~since ~amount)
      | Per_iteration { rules; _ } ->
          List.iter
            (fun (gain, per) ->
              Facts.assume context head
                (make_count_bound ~counter:cost.counter
                   ~at:(Logic.add at_head (cost.measure_gained gain head))
                   ~bound:(Logic.add cost.entry (Logic.multiply iterations per))))
            rules)
    loop.costs;
  head

let make_step_cost (counter : Costs.counter) =
  match counter.resource with
  | Metric Time -> Logic.int 1
  | Metric (Allocations | Allocated_bytes) | Calls _ -> Costs.zero

let spend_step context frame = Counters.spend context frame make_step_cost

let find_constant_count bounds =
  List.find_map
    (fun bound ->
      match Logic.normalize_linear bound with
      | Logic.Integer count when Z.gt count Z.one -> Some count
      | _ -> None)
    bounds

let is_written_in_home_package (context : State.context) callee =
  match context.lookups.mir.find_form_origin callee with
  | Some (Written key, _) ->
      Path.compare_package (Path.locate_package key.path) (Path.locate_package context.home.path)
      = 0
  | Some ((Derived _ | Inherited _), _) | None -> false

let explain_uncounted_potential context (call : State.call_amount) metric : Catalog.Prover.unbounded
    =
  Uncounted_potential
    {
      metric;
      callee = call.callee;
      call = call.call;
      is_editable = is_written_in_home_package context call.callee;
    }

let describe_part context frame (part : State.changed_part) : Catalog.Prover.changed_part =
  { root = Facts.describe_local context frame part.root; fields = part.fields }

let explain_changing_cost context (head : State.frame) (call : State.call_amount)
    ~(changed : State.changed_part list) ~parts : Catalog.Prover.unbounded =
  let is_mentioned = function
    | Some (_, term) -> List.exists (fun part -> Costs.mentions_part ~part:term part) parts
    | None -> false
  in
  Changing_cost
    {
      is_amortized = List.exists Costs.mentions_potential parts;
      call = call.call;
      values =
        List.filter_map
          (fun part ->
            if is_mentioned (Validity.find_changed_part context head part) then
              Some (describe_part context head part)
            else None)
          changed;
    }

let explain_unbounded_iteration (context : State.context) (head : State.frame)
    (counter : Costs.counter) ~changed ~parts : Catalog.Prover.unbounded =
  let list_call_parts (call : State.call_amount) =
    if call.counter = counter then
      List.filter (fun part -> Costs.mentions_part ~part call.amount) parts
    else []
  in
  let calls =
    List.filter (fun call -> list_call_parts call <> []) (List.rev context.cost.call_amounts)
  in
  let unstated =
    List.fold_left
      (fun callees (call : State.call_amount) ->
        if call.states_cost || List.exists (Path.equal call.callee) callees then callees
        else callees @ [ call.callee ])
      [] calls
  in
  match (counter.resource, unstated, calls) with
  | Metric metric, _ :: _, _ ->
      Unstated_costs
        {
          metric;
          callees = unstated;
          editable = List.filter (is_written_in_home_package context) unstated;
          counts_units = counter.counting = Units;
        }
  | Metric metric, [], call :: _
    when counter.amortized && (not call.counts_potential)
         && List.exists Costs.mentions_potential (list_call_parts call) ->
      explain_uncounted_potential context call metric
  | Metric _, [], call :: _ ->
      explain_changing_cost context head call ~changed ~parts:(list_call_parts call)
  | (Metric _ | Calls _), _, _ -> Unbounded_iteration

let assumes_recursive_costs (context : State.context) loop =
  context.cost.recursive_costs_assumed > loop.recursive_costs_mark

let check_iterations context loop_at (head : State.frame) loop ~iterations ~iteration_bounds
    ~(inside : State.frame) ~ends ~breaks =
  let location = Facts.locate context head.source loop_at in
  let facts =
    Fact_list.list_newest_since context.facts ~count:loop.facts_mark @ [ inside.condition ]
  in
  let frames = ends @ breaks and varies = Facts.mentions_fresh_after context loop.fresh_mark in
  let constant_count =
    if assumes_recursive_costs context loop then None
    else
      Option.bind iterations (fun iterations ->
          Option.map (fun count -> (iterations, count)) (find_constant_count iteration_bounds))
  in
  List.iter
    (fun cost ->
      Conditions.with_obligation_condition context cost.holds_when @@ fun () ->
      let measure_spent (frame : State.frame) =
        Costs.since
          ~start:(Counters.lookup_spent head cost.counter)
          (Counters.lookup_spent frame cost.counter)
      in
      let spends_potential =
        List.exists (fun frame -> Costs.mentions_potential (measure_spent frame)) frames
      in
      match cost.rule with
      | Clause_bound clause ->
          let moves_in_potential () =
            let held_at_head =
              Costs.list_potentials
                (Logic.normalize_linear (cost.measure_gained Whole_potential head))
            in
            let is_moved_in term =
              Costs.mentions_potential term && not (List.mem term held_at_head)
            in
            List.exists
              (fun frame -> Costs.grows_with ~varies:is_moved_in (measure_spent frame))
              frames
          in
          clause.gain <-
            (if Option.is_none clause.gained_at_head || not spends_potential then No_gain
             else if moves_in_potential () then Potential_without_elements
             else Whole_potential);
          Option.iter
            (fun gained ->
              Facts.add_frame_fact context head
                (Logic.equal gained (cost.measure_gained clause.gain head)))
            clause.gained_at_head;
          List.iter
            (fun (frame, moment) ->
              oblige_clause context frame cost clause.written ~moment
                ~since:
                  (Logic.add
                     (Logic.subtract (Counters.lookup_spent frame cost.counter) cost.entry)
                     (cost.measure_gained clause.gain frame)))
            (List.map (fun exit_frame -> (exit_frame, Catalog.Prover.After_iteration)) ends
            @ List.map (fun exit_frame -> (exit_frame, Catalog.Prover.Where_left)) breaks)
      | Per_iteration per_iteration -> (
          let facts = facts @ List.map (fun (frame : State.frame) -> frame.condition) frames in
          let measure_most (gain, per) =
            let gained_before = cost.measure_gained gain head in
            let measure_iteration (frame : State.frame) =
              let gained = Logic.subtract (cost.measure_gained gain frame) gained_before in
              if gain = No_gain then measure_spent frame
              else Logic.normalize_linear (Logic.add (measure_spent frame) gained)
            in
            let spent = List.map measure_iteration frames in
            let amortize amount = Logic.normalize_linear (Costs.take_potential_as_zero amount) in
            let most =
              match
                if gain = Potential_without_elements then List.map amortize spent else spent
              with
              | [] -> Costs.zero
              | first :: rest -> List.fold_left Logic.larger first rest
            in
            (per, spent, most)
          in
          let rec find_bounded unbounded = function
            | [] -> Error unbounded
            | (gain, _) :: rules when gain <> No_gain && not spends_potential ->
                find_bounded unbounded rules
            | ((gain, _) as rule) :: rules -> (
                let per, spent, most = measure_most rule in
                match Costs.find_cost_bound ~varies ~facts most with
                | Some bound -> Ok (gain, per, spent, bound)
                | None ->
                    find_bounded
                      (if gain = Whole_potential_deducted then unbounded else most :: unbounded)
                      rules)
          in
          match find_bounded [] per_iteration.rules with
          | Ok (gain, per, spent, bound) ->
              Facts.add_frame_fact context head (Logic.equal per bound);
              (match constant_count with
              | Some (iterations, count)
                when cost.counter.counting = Units && gain = No_gain && not spends_potential ->
                  let spent_at_head = Counters.lookup_spent head cost.counter in
                  let bound = Logic.add cost.entry (Logic.at_least_zero per) in
                  Facts.assume context head
                    Logic.(less_equal iterations (Integer count) ==> less_equal spent_at_head bound);
                  per_iteration.one_iteration_bound <- Some { spent_at_head; bound }
              | _ -> ());
              List.iter2
                (fun (frame : State.frame) spent ->
                  Facts.oblige context frame location Iteration_above_inferred_bound
                    (make_count_bound ~counter:cost.counter ~at:spent ~bound:per))
                frames spent
          | Error unbounded ->
              let parts =
                match List.map (Costs.list_unbounded_parts ~varies ~facts) unbounded with
                | [] -> []
                | first :: rest -> List.filter (fun part -> List.for_all (List.mem part) rest) first
              in
              Facts.oblige context head location
                (Unbounded_iteration_cost
                   (explain_unbounded_iteration context head cost.counter ~changed:loop.changed
                      ~parts))
                (Logic.Boolean false)))
    loop.costs

let leave context ~(clause_at : State.frame) (exit_ : State.frame) loop ~iterations ~most =
  let iterations = Option.value iterations ~default:Costs.zero in
  let assumes_recursive_costs = assumes_recursive_costs context loop in
  let spent =
    List.map
      (fun cost ->
        let at = Counters.lookup_spent exit_ cost.counter in
        match cost.rule with
        | Clause_bound { written; gain; _ } ->
            let amount = read_amount context { clause_at with makes_obligations = false } written in
            let counted =
              match cost.counter.counting with
              | Units when assumes_recursive_costs -> Costs.bound amount
              | Units -> Costs.units amount
              | At_most -> Amounts.declare_bounded_amount context exit_ amount
              | Exactly -> amount
            in
            ( cost.counter,
              Logic.add
                (Logic.subtract (Logic.add cost.entry counted) (cost.measure_gained gain clause_at))
                (Costs.since ~start:(Counters.lookup_spent clause_at cost.counter) at) )
        | Per_iteration { rules; one_iteration_bound } -> (
            List.iter
              (fun (gain, per) ->
                let banked = Logic.add at (cost.measure_gained gain exit_) in
                if cost.counter.counting <> Exactly then
                  List.iter
                    (fun most ->
                      Facts.add_frame_fact context exit_
                        Logic.(
                          conjunction
                            [
                              less_equal banked (add cost.entry (multiply iterations per));
                              less_equal (int 0) iterations;
                              less_equal iterations most;
                              less_equal (int 0) per;
                            ]
                          ==> less_equal banked (add cost.entry (multiply most per))))
                    most)
              rules;
            ( cost.counter,
              match one_iteration_bound with
              | Some { spent_at_head; bound } ->
                  Logic.add bound (Costs.since ~start:spent_at_head at)
              | None -> at )))
      loop.costs
  in
  { exit_ with spent }

let leave_counted (context : State.context) ~clause_at exit_ loop ~iterations ~most ~count ~since =
  let facts =
    Fact_list.list_newest_since context.facts ~count:since
    @ Fact_list.list_newest_since context.facts ~count:loop.facts_mark
  in
  leave context ~clause_at exit_ loop ~iterations
    ~most:
      (most
      @ Costs.list_upper_bounds
          ~varies:(Facts.mentions_fresh_after context loop.fresh_mark)
          ~facts count)
