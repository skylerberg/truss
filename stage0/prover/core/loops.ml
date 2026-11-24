type gain = No_gain | Whole_potential | Potential_without_elements
type one_iteration_bound = { spent_at_head : Logic.term; bound : Logic.term }

type loop_rule =
  | Clause_bound of { written : Mir.cost; gained_at_head : Logic.term option; mutable gain : gain }
  | Per_iteration of {
      rules : (gain * Logic.term) list;
      mutable one_iteration_bound : one_iteration_bound option;
    }

type loop_cost = {
  counter : Costs.counter;
  entry : Logic.term;
  rule : loop_rule;
  measure_gained : gain -> State.frame -> Logic.term;
}

type received = {
  has_another : Logic.term;
  element : Logic.term;
  through : Logic.term;
  advance : State.frame -> State.frame;
}

type loop_start = {
  loop_costs : loop_cost list;
  fresh_mark : int;
  facts_mark : int;
  recursive_costs_mark : int;
  preserved :
    (Obligation.message * Types.ty * Logic.term * (State.frame -> Logic.term option)) list;
  havocked : State.frame;
}

type while_loop = {
  while_at : Core.origin;
  while_clauses : Mir.loop_clause list;
  changed : State.changed;
  bind_parts : State.frame -> State.frame;
  test : State.frame -> (State.frame * Logic.term) option;
  run_body : State.frame -> State.frame list * State.frame list;
  on_failure : State.frame -> State.frame option;
  measure_operands : (Language.Comparison.t * (State.frame -> Logic.term * Logic.term)) option;
}

type iterable =
  | Over_range of { low : Logic.term; high : Logic.term; inclusive : bool }
  | Over_cursor of {
      cursor : State.passed_place;
      cursor_type : Types.ty;
      next : Invocation.t;
      next_origin : Core.origin;
    }

type for_loop = {
  for_at : Core.origin;
  for_clauses : Mir.loop_clause list;
  iterable : iterable;
  element_type : Types.ty;
  lent_element : Types.ty option;
  invariant_count : (State.frame -> Logic.term) option;
  collection : (State.frame -> Types.ty * Logic.term) option;
  element_call : (State.frame -> Logic.term) option;
  bind_element : State.frame -> Logic.term -> State.frame;
  compute_changed_in : State.frame -> State.changed;
  compute_changed_by_body : State.frame -> State.changed;
  run_body : State.frame -> Logic.term -> State.frame list * State.frame list;
  bind_parts : State.frame -> State.frame;
}

let find_clause_condition : Mir.loop_clause -> Types.condition = function
  | Invariant invariant -> invariant.holds_when
  | Decreases (measure :: _) -> measure.holds_when
  | Decreases [] -> []
  | Cost cost -> cost.holds_when

let keep_holding_clauses context (clauses : Mir.loop_clause list) =
  List.filter (fun clause -> Conditions.holds_here context (find_clause_condition clause)) clauses

let list_loop_costs context (frame : State.frame) (clauses : Mir.loop_clause list) ~held_gains =
  List.map
    (fun (counter : Costs.counter) ->
      let gains, measure_gained = Lazy.force held_gains in
      let entry =
        match List.assoc_opt counter frame.spent with Some term -> term | None -> Costs.zero
      in
      let written =
        List.find_map
          (fun (clause : Mir.loop_clause) ->
            match clause with
            | Cost cost
              when Amounts.is_same_resource cost ~locals:frame.locals counter
                   && Lambdas.classify_counting cost = counter.counting ->
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
            let needs_whole_potential = counter.amortized || counter.counting = Exactly in
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
      { counter; entry; rule; measure_gained })
    context.counters

let loop_clause_holds context (at : State.frame) (counter : Costs.counter) (cost : Mir.cost) ~since
    =
  let amount =
    match cost.bound with
    | Order_of amount | At_most amount | Exactly amount ->
        snd (Validity.read_specification context { at with makes_obligations = false } amount)
  in
  match counter.counting with
  | Units -> Logic.less_equal since (Costs.bound amount)
  | Exactly -> Logic.equal since amount
  | At_most -> Logic.less_equal since amount

let lookup_spent (frame : State.frame) key =
  match List.assoc_opt key frame.spent with Some spent_term -> spent_term | None -> Costs.zero

let make_count_bound ~(counter : Costs.counter) ~at ~bound =
  if counter.counting = Exactly then Logic.equal at bound else Logic.less_equal at bound

let enter_loop_head context head costs ~iterations =
  let iterations = Option.value iterations ~default:Costs.zero in
  let head =
    {
      head with
      State.spent =
        List.map
          (fun cost -> (cost.counter, Facts.declare_fresh context head "spent" Logic.Int))
          costs;
    }
  in
  List.iter
    (fun cost ->
      let at_head = lookup_spent head cost.counter in
      match cost.rule with
      | Clause_bound { written; gained_at_head; _ } ->
          Facts.assume context head
            (loop_clause_holds context head cost.counter written
               ~since:
                 (Costs.plus (Costs.minus at_head cost.entry)
                    (Option.value gained_at_head ~default:Costs.zero)))
      | Per_iteration { rules; _ } ->
          List.iter
            (fun (gain, per) ->
              Facts.assume context head
                (make_count_bound ~counter:cost.counter
                   ~at:(Costs.plus at_head (cost.measure_gained gain head))
                   ~bound:(Costs.plus cost.entry (Costs.times iterations per))))
            rules)
    costs;
  head

let check_loop_entry context frame costs =
  List.iter
    (fun cost ->
      match cost.rule with
      | Clause_bound { written; _ } ->
          (match written.bound with
          | Order_of amount | At_most amount | Exactly amount ->
              ignore (Validity.read_specification context frame amount));
          Facts.oblige context frame Cost
            (Facts.locate context frame.source written.origin)
            [
              Text "The loop's `";
              Facts.quote frame.source written.origin;
              Text "` may not hold on entry to the loop.";
            ]
            (loop_clause_holds context frame cost.counter written ~since:Costs.zero)
      | Per_iteration _ -> ())
    costs

let find_constant_count bounds =
  List.find_map
    (fun bound ->
      match Costs.normalize bound with
      | Logic.Integer count when Z.gt count Z.one -> Some count
      | _ -> None)
    bounds

let check_loop_iterations context loop_at (head : State.frame) (start : loop_start) ~iterations
    ~iteration_bounds ~facts ~ends ~breaks =
  let location = Facts.locate context head.source loop_at in
  let frames = ends @ breaks and varies = Facts.mentions_fresh_after context start.fresh_mark in
  let constant_count =
    if context.recursive_costs_assumed > start.recursive_costs_mark then None
    else
      Option.bind iterations (fun iterations ->
          Option.map (fun count -> (iterations, count)) (find_constant_count iteration_bounds))
  in
  List.iter
    (fun cost ->
      let measure_spent (frame : State.frame) =
        Costs.since ~start:(lookup_spent head cost.counter) (lookup_spent frame cost.counter)
      in
      let spends_potential =
        List.exists (fun frame -> Facts.mentions_potential (measure_spent frame)) frames
      in
      match cost.rule with
      | Clause_bound clause ->
          let moves_in_potential () =
            let held_at_head =
              Facts.list_potentials (Costs.normalize (cost.measure_gained Whole_potential head))
            in
            let is_moved_in term =
              Facts.mentions_potential term && not (List.mem term held_at_head)
            in
            List.exists
              (fun frame -> Costs.grows_with ~varies:is_moved_in (measure_spent frame))
              frames
          in
          clause.gain <-
            (if Option.is_none clause.gained_at_head || not spends_potential then No_gain
             else if (not cost.counter.amortized) && moves_in_potential () then
               Potential_without_elements
             else Whole_potential);
          Option.iter
            (fun gained ->
              Facts.add_frame_fact context head
                (Logic.equal gained (cost.measure_gained clause.gain head)))
            clause.gained_at_head;
          List.iter
            (fun (frame, when_) ->
              Facts.oblige context frame Cost
                (Facts.locate context frame.source clause.written.origin)
                [
                  Text "The loop's `";
                  Facts.quote frame.source clause.written.origin;
                  Text (Printf.sprintf "` may not hold %s." when_);
                ]
                (loop_clause_holds context frame cost.counter clause.written
                   ~since:
                     (Costs.plus
                        (Costs.minus (lookup_spent frame cost.counter) cost.entry)
                        (cost.measure_gained clause.gain frame))))
            (List.map (fun exit_frame -> (exit_frame, "after an iteration")) ends
            @ List.map (fun exit_frame -> (exit_frame, "where the loop is left")) breaks)
      | Per_iteration per_iteration -> (
          let facts = facts @ List.map (fun (frame : State.frame) -> frame.condition) frames in
          let find_bounded (gain, per) =
            if gain <> No_gain && not spends_potential then None
            else
              let gained_before = cost.measure_gained gain head in
              let measure_iteration (frame : State.frame) =
                let gained = Costs.minus (cost.measure_gained gain frame) gained_before in
                if gain = No_gain then measure_spent frame
                else Costs.normalize (Costs.plus (measure_spent frame) gained)
              in
              let spent = List.map measure_iteration frames in
              let amortize amount = Costs.normalize (Facts.take_potential_as_zero amount) in
              let most =
                match
                  if gain = Potential_without_elements then List.map amortize spent else spent
                with
                | [] -> Costs.zero
                | first :: rest -> List.fold_left Costs.larger first rest
              in
              Option.map
                (fun bound -> (gain, per, spent, bound))
                (Costs.find_cost_bound ~varies ~facts most)
          in
          match List.find_map find_bounded per_iteration.rules with
          | Some (gain, per, spent, bound) ->
              Facts.add_frame_fact context head (Logic.equal per bound);
              (match constant_count with
              | Some (iterations, count)
                when cost.counter.counting = Units && gain = No_gain && not spends_potential ->
                  let spent_at_head = lookup_spent head cost.counter in
                  let bound = Costs.plus cost.entry (Costs.at_least_zero per) in
                  Facts.assume context head
                    Logic.(less_equal iterations (Integer count) ==> less_equal spent_at_head bound);
                  per_iteration.one_iteration_bound <- Some { spent_at_head; bound }
              | _ -> ());
              List.iter2
                (fun (frame : State.frame) spent ->
                  Facts.oblige context frame Cost location
                    [
                      Text
                        "The prover cannot show that this iteration of the loop costs no more than \
                         the per-iteration bound it inferred from the values the loop does not \
                         mutate: give the loop a `cost` clause.";
                    ]
                    (make_count_bound ~counter:cost.counter ~at:spent ~bound:per))
                frames spent
          | None ->
              Facts.oblige context head Cost location
                [
                  Text
                    "The prover cannot bound the cost of one iteration of this loop by the values \
                     the loop does not mutate, so it cannot count the loop's cost: give the loop a \
                     `cost` clause.";
                ]
                (Logic.Boolean false)))
    start.loop_costs

let exit_loop context ~(clause_at : State.frame) (exit_ : State.frame) costs ~iterations ~most =
  let iterations = Option.value iterations ~default:Costs.zero in
  let spent =
    List.map
      (fun cost ->
        let at = lookup_spent exit_ cost.counter in
        match cost.rule with
        | Clause_bound { written; gain; _ } ->
            let amount =
              match written.bound with
              | Order_of amount | At_most amount | Exactly amount ->
                  snd
                    (Validity.read_specification context
                       { clause_at with makes_obligations = false }
                       amount)
            in
            let counted =
              match cost.counter.counting with
              | Units -> Costs.units amount
              | At_most -> Amounts.declare_bounded_amount context exit_ amount
              | Exactly -> amount
            in
            ( cost.counter,
              Costs.plus
                (Costs.minus (Costs.plus cost.entry counted) (cost.measure_gained gain clause_at))
                (Costs.since ~start:(lookup_spent clause_at cost.counter) at) )
        | Per_iteration { rules; one_iteration_bound } -> (
            List.iter
              (fun (gain, per) ->
                let banked = Costs.plus at (cost.measure_gained gain exit_) in
                if cost.counter.counting <> Exactly then
                  List.iter
                    (fun most ->
                      Facts.add_frame_fact context exit_
                        Logic.(
                          conjunction
                            [
                              less_equal banked (Costs.plus cost.entry (Costs.times iterations per));
                              less_equal (int 0) iterations;
                              less_equal iterations most;
                              less_equal (int 0) per;
                            ]
                          ==> less_equal banked (Costs.plus cost.entry (Costs.times most per))))
                    most)
              rules;
            ( cost.counter,
              match one_iteration_bound with
              | Some { spent_at_head; bound } ->
                  Costs.plus bound (Costs.since ~start:spent_at_head at)
              | None -> at )))
      costs
  in
  { exit_ with spent }

let measure_held_gains context (entry : State.frame) (changed : State.changed) =
  let held =
    List.filter_map
      (fun id ->
        Option.map
          (fun ty -> (ty, fun (at : State.frame) -> Locals.find_opt id at.locals))
          (Facts.find_local_type context entry id))
      changed.changed_locals
    @
    match (changed.changes_self, entry.self_type) with
    | true, Some ty -> [ (ty, fun (at : State.frame) -> at.self) ]
    | _ -> []
  in
  let sum_held measure (at : State.frame) =
    List.fold_left
      (fun total (ty, read) ->
        match read at with Some term -> Costs.plus total (measure at ty term) | None -> total)
      Costs.zero held
  in
  let measure_whole = sum_held (fun at ty term -> Amounts.compute_potential context at ty term)
  and measure_elements =
    sum_held (fun _ ty term -> Amounts.compute_elements_potential context ty term)
  and holds_potential = List.exists (fun (ty, _) -> Amounts.has_potential context ty) held in
  lazy
    (let whole_on_entry = measure_whole entry in
     let elements_on_entry = measure_elements entry in
     let rec measure_gained gain (at : State.frame) =
       match gain with
       | No_gain -> Costs.zero
       | Whole_potential -> Costs.minus (measure_whole at) whole_on_entry
       | Potential_without_elements ->
           Costs.minus
             (measure_gained Whole_potential at)
             (Costs.minus (measure_elements at) elements_on_entry)
     in
     ( (if holds_potential then [ Whole_potential ] else [])
       @ (No_gain :: (if elements_on_entry = Costs.zero then [] else [ Potential_without_elements ])),
       measure_gained ))

let havoc context frame (changed : State.changed) =
  let frame =
    List.fold_left
      (fun frame local ->
        let ty =
          match Facts.find_local_type context frame local with
          | Some ty -> ty
          | None -> Types.Integer
        in
        { frame with locals = Locals.add local (Facts.arrive context frame "loop" ty) frame.locals })
      frame changed.changed_locals
  in
  match (changed.changes_self, frame.self_type) with
  | true, Some ty -> { frame with self = Some (Facts.arrive context frame "loop" ty) }
  | _ -> frame

let list_validity_obligations context (entry : State.frame) (changed : State.changed) =
  let find_obligation described ty before read =
    match Validity.make_validity context entry ~assuming:false ~deep:true ty before with
    | Logic.Boolean true -> None
    | valid -> Some (described, ty, valid, read)
  in
  let describe local : Obligation.message =
    match
      ( Tables.Local_table.find_opt context.local_names local,
        Tables.Local_table.find_opt context.local_origins local )
    with
    | Some name, _ -> [ Text (Printf.sprintf "`%s`" name) ]
    | None, Some origin -> [ Text "`"; Facts.quote entry.source origin; Text "`" ]
    | None, None -> [ Text "a temporary" ]
  in
  List.filter_map
    (fun local ->
      match (Facts.find_local_type context entry local, Locals.find_opt local entry.locals) with
      | Some ty, Some before ->
          find_obligation (describe local) ty before (fun (at : State.frame) ->
              Locals.find_opt local at.locals)
      | _ -> None)
    changed.changed_locals
  @
  match (changed.changes_self, entry.self, entry.self_type) with
  | true, Some before, Some ty ->
      Option.to_list
        (find_obligation [ Obligation.Text "`self`" ] ty before (fun (at : State.frame) -> at.self))
  | _ -> []

let assume_preserved_validity context head preserved =
  List.iter
    (fun (_, ty, valid_on_entry, read) ->
      match read head with
      | Some term ->
          Facts.assume context head
            (Logic.( ==> ) valid_on_entry
               (Validity.make_validity context head ~assuming:true ~deep:true ty term))
      | None -> ())
    preserved

let check_preserved_validity context end_ location preserved =
  List.iter
    (fun (described, ty, valid_on_entry, read) ->
      match read end_ with
      | Some term ->
          Facts.oblige context end_ Invariant location
            (Obligation.Text
               (Printf.sprintf "The invariant of `%s` may not hold for " (Types.show ty))
             :: described
            @ [ Text " after an iteration." ])
            (Logic.( ==> ) valid_on_entry
               (Validity.make_validity context end_ ~assuming:false ~deep:true ty term))
      | None -> ())
    preserved

let check_invariants context frame clauses ~when_ =
  List.iter
    (fun (invariant : Mir.formula) ->
      let _, term =
        Conditions.with_obligation_condition context invariant.holds_when (fun () ->
            Validity.read_specification context frame invariant)
      in
      Facts.oblige context frame Invariant ~holds_when:invariant.holds_when
        (Facts.locate context frame.source invariant.origin)
        [
          Text "The loop invariant `";
          Facts.quote frame.source invariant.origin;
          Text (Printf.sprintf "` may not hold %s." when_);
        ]
        term)
    (Validity.list_invariants clauses)

let assume_invariants context frame clauses =
  List.iter
    (fun (invariant : Mir.formula) ->
      let _, term =
        Validity.read_specification context { frame with makes_obligations = false } invariant
      in
      Facts.assume context frame term)
    (Validity.list_invariants clauses)

let find_measures (clauses : Mir.loop_clause list) =
  List.find_map (function Mir.Decreases measures -> Some measures | _ -> None) clauses

let enter_loop ?holds context frame ~entry clauses ~changed =
  let holds = Option.value holds ~default:changed in
  let costs =
    list_loop_costs context frame clauses ~held_gains:(measure_held_gains context frame holds)
  in
  check_loop_entry context entry costs;
  let fresh_mark = context.fresh and facts_mark = List.length context.facts in
  let preserved = list_validity_obligations context frame changed in
  let head = havoc context frame changed in
  assume_preserved_validity context head preserved;
  {
    loop_costs = costs;
    fresh_mark;
    facts_mark;
    recursive_costs_mark = context.recursive_costs_assumed;
    preserved;
    havocked = head;
  }

let end_scope ~(outer : State.frame) (frame : State.frame) =
  { frame with locals = Locals.filter (fun id _ -> Locals.mem id outer.locals) frame.locals }

let leave_loop context frame frames =
  Option.map (end_scope ~outer:frame) (Facts.join_frames context frames)

let end_iterations context (frame : State.frame) loop_at clauses (start : loop_start) ~head
    ~(inside : State.frame) ~iterations ~iteration_bounds ~ends ~breaks ~with_through =
  check_loop_iterations context loop_at head start ~iterations ~iteration_bounds
    ~facts:(Lambdas.list_facts_since context start.facts_mark @ [ inside.condition ])
    ~ends:(List.map with_through ends) ~breaks:(List.map with_through breaks);
  List.iter
    (fun (end_ : State.frame) ->
      check_invariants context (with_through end_) clauses ~when_:"after an iteration";
      check_preserved_validity context end_
        (Facts.locate context frame.source loop_at)
        start.preserved)
    ends

let compute_iterations_so_far context head costs =
  if
    List.exists
      (fun (cost : loop_cost) ->
        match cost.rule with Per_iteration _ -> true | Clause_bound _ -> false)
      costs
  then begin
    let iterations = Facts.declare_fresh context head "iterations" Logic.Int in
    Facts.assume context head (Logic.less_equal (Logic.int 0) iterations);
    Some iterations
  end
  else None

let make_step_cost (counter : Costs.counter) =
  match counter.resource with
  | Metric Time -> Logic.int 1
  | Metric (Allocations | Allocated_bytes) | Calls _ -> Costs.zero

let declare_elements_so_far context (head : State.frame) ~element ~collection ~count yielded
    find_element_at =
  let symbol = Facts.make_fresh_name context "position" in
  let position = Logic.Symbol symbol in
  let premise = Logic.(less_equal (int 0) position &&& less position count) in
  (match Models.index_sequence context element yielded position with
  | Some earlier ->
      let _, same, with_facts =
        Models.run_under_binder context
          { head with bound = symbol :: head.bound; makes_obligations = false }
          symbol Logic.Int premise
          (fun inner -> Option.map (Logic.equal earlier) (find_element_at inner position))
      in
      Option.iter
        (fun same ->
          Facts.assume context head
            (with_facts (Logic.forall ([ (symbol, Logic.Int) ], Logic.( ==> ) premise same))))
        same
  | None -> ());
  match collection with
  | Some read ->
      let collection_type, collected = read head in
      Option.iter
        (Values.assume_extensional context head (Models.make_sequence_type element) yielded)
        (Models.find_model context
           (Facts.substitute_type context head collection_type)
           collected ~element)
  | None -> ()

let prove_receiving_loop ~prove_iteration ~most ~(for_loop : for_loop) context frame ~element_type
    ~changed ~holds ~start ~receive =
  let clauses = for_loop.for_clauses in
  let entry =
    { frame with State.yielded = Some (Intrinsics.make_empty_parts context frame element_type) }
  in
  check_invariants context entry clauses ~when_:"on entry to the loop";
  let loop = enter_loop ~holds context frame ~entry clauses ~changed in
  let costs = loop.loop_costs and head = for_loop.bind_parts loop.havocked in
  let before = start head in
  let iterations = Models.make_sequence_length context element_type before in
  let head =
    enter_loop_head context { head with yielded = Some before } costs ~iterations:(Some iterations)
  in
  assume_invariants context head clauses;
  let ended_mark = List.length context.facts in
  let received = receive head before in
  let through = received.through in
  let inside = received.advance (Facts.restrict head received.has_another) in
  let inside = { (Operations.spend context inside make_step_cost) with yielded = frame.yielded } in
  let ends, breaks = for_loop.run_body inside received.element in
  prove_iteration ~head ~ends;
  let with_through (exit_frame : State.frame) = { exit_frame with yielded = Some through } in
  end_iterations context frame for_loop.for_at clauses loop ~head ~inside
    ~iterations:(Some iterations) ~iteration_bounds:most ~ends ~breaks ~with_through;
  let ended = received.advance (Facts.restrict head (Logic.not_ received.has_another)) in
  let varies = Facts.mentions_fresh_after context loop.fresh_mark in
  let ended_facts =
    Lambdas.list_facts_since context ended_mark @ Lambdas.list_facts_since context loop.facts_mark
  in
  let exit_ =
    exit_loop context ~clause_at:head
      { ended with yielded = Some before }
      costs ~iterations:(Some iterations)
      ~most:(most @ Costs.list_upper_bounds ~varies ~facts:ended_facts iterations)
  in
  let left =
    List.map
      (fun (exit_frame : State.frame) ->
        let left_at = with_through exit_frame in
        exit_loop context ~clause_at:left_at left_at costs
          ~iterations:(Some (Costs.plus iterations (Logic.int 1)))
          ~most:
            (most
            @ Costs.list_upper_bounds ~varies ~facts:ended_facts
                (Models.make_sequence_length context element_type through)))
      breaks
  in
  leave_loop context frame
    (List.map
       (fun (exit_frame : State.frame) -> { exit_frame with yielded = frame.yielded })
       (exit_ :: left))

let cursor_trait : Path.t = Well_known.make_path Cursor

let declare_some_parts context frame element =
  let parts =
    Facts.declare_fresh context frame "parts"
      (Facts.declare_sort context (Models.make_sequence_type element))
  in
  Facts.assume context frame
    Logic.(greater_equal (Models.make_sequence_length context element parts) (int 0));
  parts

let names_visited (clauses : Mir.loop_clause list) =
  List.exists
    (function
      | Mir.Invariant invariant -> Amounts.mentions_history invariant
      | Decreases measures -> List.exists Amounts.mentions_history measures
      | Cost { bound = Order_of bound | At_most bound | Exactly bound; _ } ->
          Amounts.mentions_history bound)
    clauses

let assume_visited_is_a_prefix context (head : State.frame) ~element ~visited ~entry_model ~model =
  let length = Models.make_sequence_length context element in
  let position = Facts.make_fresh_name context "position" in
  let index = Logic.Symbol position in
  let is_below bound = Logic.(less_equal (int 0) index &&& less index bound) in
  match
    ( Models.index_sequence context element visited index,
      Models.index_sequence context element entry_model index,
      Models.index_sequence context element model index,
      Models.index_sequence context element entry_model (Costs.plus (length visited) index) )
  with
  | Some visited_value, Some entry_value, Some remaining_value, Some entry_value_ahead ->
      Facts.assume context head
        Logic.(
          equal (Costs.plus (length visited) (length model)) (length entry_model)
          &&& forall
                ([ (position, Int) ], is_below (length visited) ==> equal visited_value entry_value)
          &&& forall
                ( [ (position, Int) ],
                  is_below (length model) ==> equal remaining_value entry_value_ahead ));
      Values.assume_extensional context head (Models.make_sequence_type element) visited entry_model
  | _ -> ()

let oblige_next_gives_the_model context (after : State.frame) location ~element ~has_another ~pulled
    ~model ~model_after =
  let length = Models.make_sequence_length context element in
  let position = Facts.make_fresh_name context "position" in
  let index = Logic.Symbol position in
  match
    ( Models.index_sequence context element model (Logic.int 0),
      Models.index_sequence context element model_after index,
      Models.index_sequence context element model (Costs.plus index (Logic.int 1)) )
  with
  | Some first, Some value_after, Some value_ahead ->
      Facts.oblige context after Invariant location
        [
          Obligation.Text
            "This loop names `visited`, and the `next` of its cursor may not give the values of \
             the cursor's `model()` in order.";
        ]
        Logic.(
          has_another
          ==> (greater (length model) (int 0)
              &&& equal pulled first
              &&& equal (Costs.plus (length model_after) (int 1)) (length model)
              &&& forall
                    ( [ (position, Int) ],
                      less_equal (int 0) index
                      &&& less index (length model_after)
                      ==> equal value_after value_ahead ))
          &&& (not_ has_another ==> equal (length model) (int 0)))
  | _ -> ()

let prove_cursor_loop ~(for_loop : for_loop) context (frame : State.frame)
    (cursor_access : State.passed_place) (next : Invocation.t) ~cursor_type ~next_origin =
  let location = Facts.locate context frame.source for_loop.for_at in
  let clauses = for_loop.for_clauses in
  ignore (cursor_access.read frame);
  let element_type = Facts.substitute_type context frame for_loop.element_type in
  let find_model (at : State.frame) =
    if names_visited clauses then
      Models.find_model context
        (Facts.substitute_type context frame cursor_type)
        (cursor_access.read at) ~element:element_type
    else None
  in
  let entry_model = find_model frame in
  let trait, evidence =
    match next.callee with
    | Trait_method { trait; evidence; _ } ->
        ( trait,
          Interface.Impls.resolve_evidence context.lookups.interface frame.substitution
            ~self_type:cursor_type ~trait evidence )
    | _ -> Facts.raise_bug "a loop over `%s` pulls no `Cursor`" (Types.show cursor_type)
  in
  let self_type = Facts.substitute_type context frame cursor_type in
  let self_binding =
    Types.bind_argument
      (Types.make_self_parameter cursor_trait)
      (Types.Type cursor_type) Types.no_substitution
  in
  let path, callee_substitution =
    match evidence with
    | Impl { impl; substitution } ->
        ( Well_known.make_impl_method_path Cursor_next ~impl,
          Types.combine_substitutions substitution self_binding )
    | Bound | Dynamic -> (Well_known.make_method_path Cursor_next, self_binding)
  in
  let cursor_next = Well_known.locate_method Cursor_next in
  let contract =
    match
      Contracts.find_method_contract context trait cursor_next.name cursor_next.receiver evidence
    with
    | Some contract ->
        Calls.add_restated_clauses context ~self_type
          ~bind:(fun subtrait _ ->
            Contracts.make_trait_substitution context.lookups subtrait self_type)
          cursor_trait cursor_next.name cursor_next.receiver contract
    | None ->
        Facts.raise_unsupported location "a loop over `%s`, whose `next` the prover cannot read"
          (Types.show cursor_type)
  in
  let option_type =
    Types.Named { path = Well_known.make_path Option; arguments = [ Types.Type element_type ] }
  in
  let pulling : Invocation.site = { origin = next_origin; type_ = option_type } in
  let measures = find_measures clauses in
  if context.terminates && measures = None then
    Facts.raise_bug "a loop over a cursor has no measure in a body that terminates";
  let find_measured (at : State.frame) =
    Option.map
      (List.map (fun measure ->
           snd (Validity.read_specification context { at with makes_obligations = false } measure)))
      measures
  in
  let entry_measure = match find_measured frame with Some [ entry ] -> Some entry | _ -> None in
  let is_amortized =
    List.exists
      (fun (next_clauses : State.clauses) ->
        List.exists (fun (cost : Mir.cost) -> cost.amortized) next_clauses.costs)
      (Contracts.list_declared_clauses contract)
  in
  let holds =
    if is_amortized then for_loop.compute_changed_in frame
    else for_loop.compute_changed_by_body frame
  in
  prove_receiving_loop ~for_loop context frame ~element_type
    ~changed:(for_loop.compute_changed_in frame)
    ~holds ~most:(Option.to_list entry_measure)
    ~prove_iteration:(fun ~head ~ends ->
      match find_measured head with
      | Some before ->
          List.iter
            (fun (end_ : State.frame) ->
              match find_measured end_ with
              | Some after ->
                  Facts.oblige context end_ Termination location
                    [ Text "This loop's measure may not decrease." ]
                    (Amounts.compare_lexicographically before after)
              | None -> ())
            ends
      | None -> ())
    ~start:(fun head ->
      let before = declare_some_parts context head element_type in
      (match (entry_measure, find_measured head) with
      | Some entry, Some [ now ] ->
          Facts.assume context head
            Logic.(
              less_equal
                (Costs.plus (Models.make_sequence_length context element_type before) now)
                entry
              &&& less_equal (Models.make_sequence_length context element_type before) entry)
      | _ -> ());
      (match (entry_model, find_model head) with
      | Some entry_model, Some model ->
          assume_visited_is_a_prefix context head ~element:element_type ~visited:before ~entry_model
            ~model
      | _ -> ());
      before)
    ~receive:(fun head before ->
      let cursor = cursor_access.read head in
      let havoc_mut (frame : State.frame) =
        cursor_access.write frame (Facts.arrive context frame "changed" cursor_type)
      in
      let recursive_callee = Facts.find_recursive_callee context head location next.callee in
      let after, pulled =
        Calls.call_contract ~recursive_callee ~lent_final:None context head pulling next path
          contract
          [
            {
              position = 0;
              mode = Language.Mode.Mut;
              shape = Other;
              origin = None;
              passed_place = Some cursor_access;
              type_ = cursor_type;
              term = cursor;
            };
          ]
          ~havoc_mut
          ~substitution_of:(fun _ -> callee_substitution)
          ~type_arguments:[ Types.Type cursor_type ]
      in
      let some_variant = Some (Well_known.show_variant Option_some) in
      let has_another = Logic.Is (Facts.make_constructor_symbol option_type some_variant, pulled) in
      let element =
        Logic.Apply
          ( Facts.make_selector_symbol option_type some_variant
              (Well_known.show_field Option_some_value),
            [ pulled ] )
      in
      (match (find_model head, find_model after) with
      | Some model, Some model_after ->
          oblige_next_gives_the_model context after location ~element:element_type ~has_another
            ~pulled:element ~model ~model_after
      | _ -> ());
      let inside = Facts.restrict after has_another in
      Validity.assume_valid context inside element_type element;
      {
        has_another;
        element;
        through = Intrinsics.append_part context inside element_type before element;
        advance =
          (fun (frame : State.frame) ->
            let now = cursor_access.read after in
            { (cursor_access.write frame now) with spent = after.spent });
      })

let run_for_loop context frame (for_loop : for_loop) =
  let clauses = for_loop.for_clauses in
  match for_loop.iterable with
  | Over_range { low; high; inclusive } ->
      let element =
        Facts.substitute_type context frame
          (Option.value for_loop.lent_element ~default:for_loop.element_type)
      in
      let over_positions = Option.is_some for_loop.lent_element in
      let find_element_at (at : State.frame) position =
        Option.map
          (fun element_of -> element_of (for_loop.bind_element at position))
          for_loop.element_call
      in
      let outer_yielded = frame.yielded in
      let bind_at_index (exit_frame : State.frame) next = for_loop.bind_element exit_frame next in
      let entry =
        bind_at_index
          { frame with yielded = Some (Intrinsics.make_empty_parts context frame element) }
          low
      in
      check_invariants context entry clauses ~when_:"on entry to the loop";
      let start =
        enter_loop context frame ~entry clauses ~changed:(for_loop.compute_changed_in frame)
      in
      let costs = start.loop_costs and head = for_loop.bind_parts start.havocked in
      let count =
        Costs.normalize
          (if inclusive then Costs.plus (Costs.minus high low) (Logic.int 1)
           else Costs.minus high low)
      in
      let iterations = Facts.declare_fresh context head "iterations" Logic.Int in
      Facts.assume context head
        Logic.(less_equal (int 0) iterations &&& less_equal iterations (Costs.at_least_zero count));
      let before = declare_some_parts context head element in
      Facts.assume context head
        (Logic.equal (Models.make_sequence_length context element before) iterations);
      (let position = Facts.make_fresh_name context "index" in
       match
         if over_positions then None
         else Models.index_sequence context element before (Logic.Symbol position)
       with
       | Some yielded_index ->
           Facts.assume context head
             (Logic.forall
                ( [ (position, Logic.Int) ],
                  Logic.(
                    less_equal (int 0) (Symbol position)
                    &&& less (Symbol position) iterations
                    ==> equal yielded_index (add low (Symbol position))) ))
       | None -> ());
      Option.iter
        (fun _ ->
          declare_elements_so_far context head ~element ~collection:for_loop.collection
            ~count:iterations before find_element_at)
        for_loop.element_call;
      let index = Costs.plus low iterations in
      let head =
        enter_loop_head context
          (bind_at_index { head with yielded = Some before } index)
          costs ~iterations:(Some iterations)
      in
      assume_invariants context head clauses;
      let find_kept_count (at : State.frame) =
        Option.map (fun count_of -> Logic.equal (count_of at) high) for_loop.invariant_count
      in
      Option.iter (Facts.assume context head)
        (find_kept_count { head with makes_obligations = false });
      let inside = Facts.restrict head (Logic.less iterations count) in
      let through =
        Intrinsics.append_part context inside element before
          (if over_positions then
             match find_element_at { inside with makes_obligations = false } index with
             | Some lent -> lent
             | None -> Facts.arrive context inside "element" element
           else index)
      in
      let inside = { inside with yielded = outer_yielded } in
      let inside = Operations.spend context inside make_step_cost in
      let ends, breaks = for_loop.run_body inside index in
      let with_through (exit_frame : State.frame) =
        bind_at_index { exit_frame with yielded = Some through } (Costs.plus index (Logic.int 1))
      in
      end_iterations context frame for_loop.for_at clauses start ~head ~inside
        ~iterations:(Some iterations) ~iteration_bounds:[ count ] ~ends ~breaks ~with_through;
      List.iter
        (fun (end_ : State.frame) ->
          Option.iter
            (Facts.oblige context end_ Invariant
               (Facts.locate context frame.source for_loop.for_at)
               [
                 Text
                   "An iteration of this loop may change how many elements the collection has. The \
                    collection's `element(mut self)` must leave its `count` as it was.";
               ])
            (find_kept_count end_))
        ends;
      let most = [ Costs.at_least_zero count ] in
      let exit_ =
        exit_loop context ~clause_at:head
          (Facts.restrict head (Logic.greater_equal iterations count))
          costs ~iterations:(Some iterations) ~most
      in
      let left =
        List.map
          (fun (exit_frame : State.frame) ->
            let left_at = with_through exit_frame in
            exit_loop context ~clause_at:left_at left_at costs
              ~iterations:(Some (Costs.plus iterations (Logic.int 1)))
              ~most)
          breaks
      in
      leave_loop context frame
        (List.map
           (fun (exit_frame : State.frame) -> { exit_frame with yielded = outer_yielded })
           (exit_ :: left))
  | Over_cursor { cursor; cursor_type; next; next_origin } ->
      prove_cursor_loop ~for_loop context frame cursor next ~cursor_type ~next_origin

let run_while_loop context (frame : State.frame) (loop : while_loop) =
  let clauses = loop.while_clauses in
  let location = Facts.locate context frame.source loop.while_at in
  check_invariants context frame clauses ~when_:"on entry to the loop";
  let start = enter_loop context frame ~entry:frame clauses ~changed:loop.changed in
  let costs = start.loop_costs and head = loop.bind_parts start.havocked in
  let iterations = compute_iterations_so_far context head costs in
  let head = enter_loop_head context head costs ~iterations in
  assume_invariants context head clauses;
  let tested = loop.test head in
  let entered =
    Option.map
      (fun (at_condition, holds) ->
        Operations.spend context (Facts.restrict at_condition holds) make_step_cost)
      tested
  in
  let ends, breaks =
    match entered with Some entered -> loop.run_body entered | None -> ([], [])
  in
  let inside =
    match entered with Some entered -> entered | None -> Facts.restrict head (Logic.Boolean false)
  in
  let measure_terms (at : State.frame) =
    let at = { at with makes_obligations = false } in
    let read measure = snd (Validity.read_specification context at measure) in
    match (find_measures clauses, loop.measure_operands) with
    | Some measures, _ -> Some (List.map read measures)
    | None, Some (comparison, read_operands) when context.terminates -> (
        let left, right = Validity.run_without_costs context (fun () -> read_operands at) in
        let distance from into = Logic.subtract into from in
        let through distance = Logic.add distance (Logic.int 1) in
        match (comparison : Language.Comparison.t) with
        | Less -> Some [ distance left right ]
        | Less_equal -> Some [ through (distance left right) ]
        | Greater -> Some [ distance right left ]
        | Greater_equal -> Some [ through (distance right left) ]
        | Equal | Not_equal -> Facts.raise_bug "an equality gives a loop its measure")
    | None, _ -> None
  in
  let start_measures = measure_terms head in
  if context.terminates && start_measures = None then
    Facts.raise_bug "a `while` loop has no measure in a body that terminates";
  let iteration_bounds =
    match (start_measures, measure_terms frame, iterations) with
    | Some [ at_head ], Some [ on_entry ], Some iterations ->
        let last = Facts.declare_fresh context head "last" Logic.Int in
        Facts.assume context head
          Logic.(
            equal iterations (int 0)
            ==> less_equal at_head on_entry
            &&& (greater_equal iterations (int 1)
                ==> (less_equal (int 0) last
                    &&& less_equal (add (subtract iterations (int 1)) last) on_entry
                    &&& less at_head last)));
        [ Costs.plus on_entry (Logic.int 1) ]
    | _ -> []
  in
  let most = List.map Costs.at_least_zero iteration_bounds in
  check_loop_iterations context loop.while_at head start ~iterations ~iteration_bounds
    ~facts:(Lambdas.list_facts_since context start.facts_mark @ [ inside.condition ])
    ~ends ~breaks;
  List.iter
    (fun (end_ : State.frame) ->
      check_invariants context end_ clauses ~when_:"after an iteration";
      check_preserved_validity context end_ location start.preserved;
      match (start_measures, measure_terms end_) with
      | Some before, Some after ->
          Facts.oblige context end_ Termination location
            [ Text "This loop's measure may not decrease." ]
            (Amounts.compare_lexicographically before after)
      | _ -> ())
    ends;
  let failing =
    Option.bind tested (fun (at_condition, holds) ->
        loop.on_failure
          (exit_loop context ~clause_at:head
             (Facts.restrict at_condition (Logic.not_ holds))
             costs ~iterations ~most))
  in
  Facts.join_frames context
    (Option.to_list failing
    @ List.map
        (fun (leaving : State.frame) ->
          exit_loop context ~clause_at:leaving leaving costs
            ~iterations:(Option.map (fun count -> Costs.plus count (Logic.int 1)) iterations)
            ~most)
        breaks)
