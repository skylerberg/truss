type loop_rule =
  | Clause_bound of Mir.cost
  | Per_iteration of { per : Logic.term; per_held : (Logic.term * Logic.term) option }

type loop_cost = {
  counter : Costs.counter;
  entry : Logic.term;
  rule : loop_rule;
  held : (State.frame -> Logic.term) option;
  held_on_entry : Logic.term option;
  gained_at_head : Logic.term option;
  mutable counts_potential : bool;
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
  preserved : (string * Types.ty * Logic.term * (State.frame -> Logic.term option)) list;
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
  measure_operands : (Core.comparison * (State.frame -> Logic.term * Logic.term)) option;
}

type iterable =
  | Over_range of { low : Logic.term; high : Logic.term; inclusive : bool }
  | Over_cursor of { cursor : State.passed_place; cursor_type : Types.ty; next : Invocation.callee }

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
  changed_in : State.frame -> State.changed;
  changed_by_body : State.frame -> State.changed;
  run_body : State.frame -> Logic.term -> State.frame list * State.frame list;
  bind_parts : State.frame -> State.frame;
}

let list_loop_costs context (frame : State.frame) (clauses : Mir.loop_clause list) ~held =
  List.map
    (fun (counter : Costs.counter) ->
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
        | Some cost -> Clause_bound cost
        | None ->
            Per_iteration
              {
                per = Facts.declare_fresh context frame "per" Logic.Int;
                per_held =
                  Option.map
                    (fun held -> (Facts.declare_fresh context frame "per" Logic.Int, held frame))
                    held;
              }
      in
      {
        counter;
        entry;
        rule;
        held;
        held_on_entry = Option.map (fun held -> held frame) held;
        gained_at_head =
          (match (rule, held) with
          | Clause_bound _, Some _ when counter.counting <> Exactly ->
              Some (Facts.declare_fresh context frame "gained" Logic.Int)
          | _ -> None);
        counts_potential = false;
      })
    context.counters

let loop_clause_holds context (at : State.frame) (counter : Costs.counter) (cost : Mir.cost) ~since
    =
  let amount =
    match cost.bound with
    | Order_of amount | At_most amount | Exactly amount ->
        snd (Validity.read_specification context { at with makes_obligations = false } amount)
    | Finite -> Costs.zero
  in
  match counter.counting with
  | Units -> Costs.at_most since (Costs.bound amount)
  | Exactly -> Logic.equal since amount
  | At_most -> Costs.at_most since amount

let compute_potential_gained (cost : loop_cost) (at : State.frame) =
  match (cost.held, cost.held_on_entry) with
  | Some held, Some on_entry when cost.counts_potential -> Costs.minus (held at) on_entry
  | _ -> Costs.zero

let lookup_spent (frame : State.frame) key =
  match List.assoc_opt key frame.spent with Some spent_term -> spent_term | None -> Costs.zero

let make_count_bound ~(counter : Costs.counter) ~at ~bound =
  if counter.counting = Exactly then Logic.equal at bound else Costs.at_most at bound

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
      | Clause_bound written ->
          Facts.assume context head
            (loop_clause_holds context head cost.counter written
               ~since:
                 (Costs.plus (Costs.minus at_head cost.entry)
                    (Option.value cost.gained_at_head ~default:Costs.zero)))
      | Per_iteration { per; per_held } -> (
          Facts.assume context head
            (make_count_bound ~counter:cost.counter ~at:at_head
               ~bound:(Costs.plus cost.entry (Costs.times iterations per)));
          match (per_held, cost.held) with
          | Some (per_held, on_entry), Some held ->
              Facts.assume context head
                (make_count_bound ~counter:cost.counter
                   ~at:(Costs.plus at_head (held head))
                   ~bound:
                     (Costs.plus (Costs.plus cost.entry on_entry) (Costs.times iterations per_held)))
          | _ -> ()))
    costs;
  head

let check_loop_entry context frame costs =
  List.iter
    (fun cost ->
      match cost.rule with
      | Clause_bound written ->
          (match written.bound with
          | Order_of amount | At_most amount | Exactly amount ->
              ignore (Validity.read_specification context frame amount)
          | Finite -> ());
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

let check_loop_iterations context loop_at (head : State.frame) costs ~mark ~facts ~ends ~breaks =
  let location = Facts.locate context head.source loop_at in
  List.iter
    (fun cost ->
      match cost.rule with
      | Clause_bound written_cost ->
          cost.counts_potential <-
            Option.is_some cost.gained_at_head
            && List.exists
                 (fun (frame : State.frame) ->
                   Facts.mentions_potential
                     (Costs.since ~start:(lookup_spent head cost.counter)
                        (lookup_spent frame cost.counter)))
                 (ends @ breaks);
          Option.iter
            (fun gained ->
              Facts.add_frame_fact context head
                (Logic.equal gained (compute_potential_gained cost head)))
            cost.gained_at_head;
          List.iter
            (fun (frame, when_) ->
              Facts.oblige context frame Cost
                (Facts.locate context frame.source written_cost.origin)
                [
                  Text "The loop's `";
                  Facts.quote frame.source written_cost.origin;
                  Text (Printf.sprintf "` may not hold %s." when_);
                ]
                (loop_clause_holds context frame cost.counter written_cost
                   ~since:
                     (Costs.plus
                        (Costs.minus (lookup_spent frame cost.counter) cost.entry)
                        (compute_potential_gained cost frame))))
            (List.map (fun exit_frame -> (exit_frame, "after an iteration")) ends
            @ List.map (fun exit_frame -> (exit_frame, "where the loop is left")) breaks)
      | Per_iteration { per; per_held } -> (
          let frames = ends @ breaks in
          let plain (frame : State.frame) =
            Costs.since ~start:(lookup_spent head cost.counter) (lookup_spent frame cost.counter)
          in
          let held_rule =
            match (per_held, cost.held) with
            | Some (per_held, _), Some held
              when List.exists
                     (fun exit_frame -> Facts.mentions_potential (plain exit_frame))
                     frames ->
                [
                  ( per_held,
                    fun (frame : State.frame) ->
                      Costs.normalize
                        (Costs.plus (plain frame) (Costs.minus (held frame) (held head))) );
                ]
            | _ -> []
          in
          let facts = facts @ List.map (fun (frame : State.frame) -> frame.condition) frames in
          let bounded (per, spent_in) =
            let spent = List.map spent_in frames in
            let most =
              match spent with
              | [] -> Costs.zero
              | first :: rest -> List.fold_left Costs.larger first rest
            in
            Option.map
              (fun bound -> (per, spent, bound))
              (Costs.find_cost_bound ~varies:(Facts.mentions_fresh_after context mark) ~facts most)
          in
          match List.find_map bounded (held_rule @ [ (per, plain) ]) with
          | Some (per, spent, bound) ->
              Facts.add_frame_fact context head (Logic.equal per bound);
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
    costs

let exit_loop context (exit_ : State.frame) costs ~iterations ~most =
  let iterations = Option.value iterations ~default:Costs.zero in
  let spent =
    List.map
      (fun cost ->
        let at = lookup_spent exit_ cost.counter in
        match cost.rule with
        | Clause_bound written ->
            let amount =
              match written.bound with
              | Order_of amount | At_most amount | Exactly amount ->
                  snd
                    (Validity.read_specification context
                       { exit_ with makes_obligations = false }
                       amount)
              | Finite -> Costs.zero
            in
            let counted =
              match cost.counter.counting with
              | Units -> Costs.units amount
              | At_most -> Amounts.declare_bounded_amount context exit_ amount
              | Exactly -> amount
            in
            ( cost.counter,
              Costs.minus (Costs.plus cost.entry counted) (compute_potential_gained cost exit_) )
        | Per_iteration { per; per_held } ->
            let bounded ~at ~start per =
              if cost.counter.counting <> Exactly then
                List.iter
                  (fun most ->
                    Facts.add_frame_fact context exit_
                      Logic.(
                        conjunction
                          [
                            Costs.at_most at (Costs.plus start (Costs.times iterations per));
                            Operation ("<=", [ int 0; iterations ]);
                            Operation ("<=", [ iterations; most ]);
                            Operation ("<=", [ int 0; per ]);
                          ]
                        ==> Costs.at_most at (Costs.plus start (Costs.times most per))))
                  most
            in
            bounded ~at ~start:cost.entry per;
            (match (per_held, cost.held) with
            | Some (per_held, on_entry), Some held ->
                bounded
                  ~at:(Costs.plus at (held exit_))
                  ~start:(Costs.plus cost.entry on_entry) per_held
            | _ -> ());
            (cost.counter, at))
      costs
  in
  { exit_ with spent }

let compute_held_potential context (frame : State.frame) (changed : State.changed) =
  let typed =
    List.filter_map
      (fun id -> Option.map (fun ty -> (`Local id, ty)) (Facts.find_local_type context frame id))
      changed.changed_locals
    @
    match (changed.changes_self, frame.self_type) with
    | true, Some ty -> [ (`Self, ty) ]
    | _ -> []
  in
  if not (List.exists (fun (_, ty) -> Amounts.has_potential context ty) typed) then None
  else
    Some
      (fun (frame : State.frame) ->
        List.fold_left
          (fun total (place, ty) ->
            match (place, frame.self) with
            | `Local id, _ -> (
                match Locals.find_opt id frame.locals with
                | Some term -> Costs.plus total (Amounts.compute_potential context frame ty term)
                | None -> total)
            | `Self, Some self -> Costs.plus total (Amounts.compute_potential context frame ty self)
            | `Self, None -> total)
          Costs.zero typed)

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
  let frame =
    {
      frame with
      slices =
        List.fold_left
          (fun slices local -> Locals.add local State.Unknown_slice slices)
          frame.slices changed.reassigned;
    }
  in
  match (changed.changes_self, frame.self_type) with
  | true, Some ty -> { frame with self = Some (Facts.arrive context frame "loop" ty) }
  | _ -> frame

let list_validity_obligations context (entry : State.frame) (changed : State.changed) =
  let obligation name ty before read =
    match Validity.make_validity context entry ~assuming:false ~deep:true ty before with
    | Logic.Boolean true -> None
    | valid -> Some (name, ty, valid, read)
  in
  List.filter_map
    (fun local ->
      match (Facts.find_local_type context entry local, Locals.find_opt local entry.locals) with
      | Some ty, Some before ->
          obligation
            (Option.value (Hashtbl.find_opt context.local_names local) ~default:"a local")
            ty before
            (fun (at : State.frame) -> Locals.find_opt local at.locals)
      | _ -> None)
    changed.changed_locals
  @
  match (changed.changes_self, entry.self, entry.self_type) with
  | true, Some before, Some ty ->
      Option.to_list (obligation "self" ty before (fun (at : State.frame) -> at.self))
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
    (fun (name, ty, valid_on_entry, read) ->
      match read end_ with
      | Some term ->
          Facts.oblige context end_ Invariant location
            [
              Text
                (Printf.sprintf "The invariant of `%s` may not hold for `%s` after an iteration."
                   (Types.show ty) name);
            ]
            (Logic.( ==> ) valid_on_entry
               (Validity.make_validity context end_ ~assuming:false ~deep:true ty term))
      | None -> ())
    preserved

let check_invariants context frame clauses ~when_ =
  List.iter
    (fun (invariant : Mir.formula) ->
      let _, term = Validity.read_specification context frame invariant in
      Facts.oblige context frame Invariant
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
    list_loop_costs context frame clauses ~held:(compute_held_potential context frame holds)
  in
  check_loop_entry context entry costs;
  let fresh_mark = context.fresh and facts_mark = List.length context.facts in
  let preserved = list_validity_obligations context frame changed in
  let head = havoc context frame changed in
  assume_preserved_validity context head preserved;
  { loop_costs = costs; fresh_mark; facts_mark; preserved; havocked = head }

let end_scope ~(outer : State.frame) (frame : State.frame) =
  { frame with locals = Locals.filter (fun id _ -> Locals.mem id outer.locals) frame.locals }

let leave_loop context frame frames =
  Option.map (end_scope ~outer:frame) (Facts.join_frames context frames)

let end_iterations context (frame : State.frame) loop_at clauses (start : loop_start) ~head
    ~(inside : State.frame) ~ends ~breaks ~with_through =
  check_loop_iterations context loop_at head start.loop_costs ~mark:start.fresh_mark
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
    Facts.assume context head (Logic.Operation ("<=", [ Logic.int 0; iterations ]));
    Some iterations
  end
  else None

let make_step_cost (counter : Costs.counter) =
  match counter.resource with Time -> Logic.int 1 | _ -> Costs.zero

let declare_elements_so_far context (head : State.frame) ~element ~collection ~count yielded
    element_at =
  let symbol = Facts.make_fresh_name context "position" in
  let position = Logic.Symbol symbol in
  let premise =
    Logic.(Operation ("<=", [ int 0; position ]) &&& Operation ("<", [ position; count ]))
  in
  (match Models.index_sequence context element yielded position with
  | Some earlier ->
      let _, same, with_facts =
        Models.under_binder context
          { head with bound = symbol :: head.bound; makes_obligations = false }
          symbol Logic.Int premise
          (fun inner -> Option.map (Logic.equal earlier) (element_at inner position))
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
      let model_type =
        Facts.substitute_type context head
          (Projection
             {
               base = collection_type;
               trait = { trait = Well_known.path Model; trait_arguments = []; associated = [] };
               name = "Value";
             })
      in
      if model_type = Models.make_sequence_type element then
        Option.iter
          (Values.assume_extensional context head model_type yielded)
          (Models.find_model context collection_type collected ~element)
  | None -> ()

let receiving_loop ~each_iteration ~most ~(for_loop : for_loop) context frame ~element_type ~changed
    ~holds ~start ~receive =
  let clauses = for_loop.for_clauses in
  let entry =
    { frame with State.yielded = Some (Amounts.make_empty_parts context frame element_type) }
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
  each_iteration ~head ~ends;
  let with_through (exit_frame : State.frame) = { exit_frame with yielded = Some through } in
  end_iterations context frame for_loop.for_at clauses loop ~head ~inside ~ends ~breaks
    ~with_through;
  let ended = received.advance (Facts.restrict head (Logic.not_ received.has_another)) in
  let varies = Facts.mentions_fresh_after context loop.fresh_mark in
  let ended_facts =
    Lambdas.list_facts_since context ended_mark @ Lambdas.list_facts_since context loop.facts_mark
  in
  let exit_ =
    exit_loop context
      { ended with yielded = Some before }
      costs ~iterations:(Some iterations)
      ~most:(most @ Costs.list_upper_bounds ~varies ~facts:ended_facts iterations)
  in
  let left =
    List.map
      (fun (exit_frame : State.frame) ->
        exit_loop context (with_through exit_frame) costs
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

let cursor_trait : Path.t = Well_known.path Cursor
let option_path : Path.t = Well_known.path Option

let declare_some_parts context frame element =
  let parts =
    Facts.declare_fresh context frame "parts"
      (Facts.declare_sort context (Models.make_sequence_type element))
  in
  Facts.assume context frame
    Logic.(Operation (">=", [ Models.make_sequence_length context element parts; int 0 ]));
  parts

let own_cursor_loop ~(for_loop : for_loop) context (frame : State.frame)
    (cursor_access : State.passed_place) (next : Invocation.callee) ~cursor_type =
  let location = Facts.locate context frame.source for_loop.for_at in
  let clauses = for_loop.for_clauses in
  ignore (cursor_access.read frame);
  let element_type = Facts.substitute_type context frame for_loop.element_type in
  let trait, evidence =
    match next with
    | Trait_method { trait; evidence = Impl _ as evidence; _ } -> (trait, evidence)
    | _ ->
        Facts.unsupported location "a loop over `%s`, whose `Cursor` the prover cannot find"
          (Types.show cursor_type)
  in
  let impl, impl_arguments =
    match evidence with
    | Impl { impl; arguments } ->
        ( impl,
          List.map
            (fun (parameter, argument) ->
              (parameter, Types.substitute_argument frame.substitution argument))
            arguments )
    | _ -> Facts.bug "a cursor's evidence is not an impl"
  in
  let contract =
    match Contracts.method_contract context.lookups trait "next" Mut evidence with
    | Some contract -> contract
    | None ->
        Facts.unsupported location "a loop over `%s`, whose `next` the prover cannot read"
          (Types.show cursor_type)
  in
  let path = Path.Method { owner = impl; name = "next"; receiver = Mut } in
  let option_type = Types.Named { path = option_path; arguments = [ Types.Type element_type ] } in
  let invocation : Invocation.t = { callee = next; lends = None; uses = Types.no_capabilities } in
  let pulling : Invocation.site = { origin = for_loop.for_at; type_ = option_type } in
  let measures = find_measures clauses in
  if context.terminates && not (Laws.signature_terminates context path) then
    Facts.oblige context frame Termination location
      [
        Text
          (Printf.sprintf "This loop may not end: `%s`'s `next` has no `time` clause."
             (Types.show cursor_type));
      ]
      (Logic.Boolean false);
  if context.terminates && measures = None then
    Facts.oblige context frame Termination location
      [
        Text
          "This loop may not end: a cursor of a type's own promises no end, so give the loop a \
           `decreases` clause.";
      ]
      (Logic.Boolean false);
  let measured (at : State.frame) =
    Option.map
      (List.map (fun measure ->
           snd (Validity.read_specification context { at with makes_obligations = false } measure)))
      measures
  in
  let entry_measure =
    if context.terminates then match measured frame with Some [ entry ] -> Some entry | _ -> None
    else None
  in
  let is_amortized =
    List.exists
      (fun (part : State.part) -> List.exists (fun (cost : Mir.cost) -> cost.amortized) part.costs)
      contract.parts
  in
  let holds = if is_amortized then for_loop.changed_in frame else for_loop.changed_by_body frame in
  receiving_loop ~for_loop context frame ~element_type ~changed:(for_loop.changed_in frame) ~holds
    ~most:(Option.to_list entry_measure)
    ~each_iteration:(fun ~head ~ends ->
      if context.terminates then
        match measured head with
        | Some before ->
            List.iter
              (fun (end_ : State.frame) ->
                match measured end_ with
                | Some after ->
                    Facts.oblige context end_ Termination location
                      [ Text "This loop's measure may not decrease." ]
                      (Amounts.compare_lexicographically before after)
                | None -> ())
              ends
        | None -> ())
    ~start:(fun head ->
      let before = declare_some_parts context head element_type in
      (match (entry_measure, measured head) with
      | Some entry, Some [ now ] ->
          Facts.assume context head
            Logic.(
              Operation
                ( "<=",
                  [
                    Costs.plus (Models.make_sequence_length context element_type before) now; entry;
                  ] )
              &&& Operation
                    ("<=", [ Models.make_sequence_length context element_type before; entry ]))
      | _ -> ());
      before)
    ~receive:(fun head before ->
      let cursor = cursor_access.read head in
      let havoc_mut (frame : State.frame) =
        cursor_access.write frame (Facts.arrive context frame "changed" cursor_type)
      in
      let after, pulled =
        Calls.contract_call ~lent_final:None context head pulling invocation path contract
          [
            {
              position = 0;
              mode = Types.Mut;
              shape = Other;
              origin = None;
              passed_place = Some cursor_access;
              type_ = cursor_type;
              term = cursor;
            };
          ]
          ~havoc_mut
          ~substitution_of:(fun _ ->
            impl_arguments @ [ (Types.make_self_parameter cursor_trait, Types.Type cursor_type) ])
          ~instance:[ Types.Type cursor_type ]
      in
      let has_another =
        Logic.Is (Facts.make_constructor_symbol option_type (Some "Some"), pulled)
      in
      let element =
        Logic.Apply (Facts.make_selector_symbol option_type (Some "Some") "value", [ pulled ])
      in
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
      let element_at (at : State.frame) position =
        Option.map
          (fun element_of -> element_of (for_loop.bind_element at position))
          for_loop.element_call
      in
      let outer_yielded = frame.yielded in
      let at_index (exit_frame : State.frame) next = for_loop.bind_element exit_frame next in
      let entry =
        at_index { frame with yielded = Some (Amounts.make_empty_parts context frame element) } low
      in
      check_invariants context entry clauses ~when_:"on entry to the loop";
      let start = enter_loop context frame ~entry clauses ~changed:(for_loop.changed_in frame) in
      let costs = start.loop_costs and head = for_loop.bind_parts start.havocked in
      let count =
        Costs.normalize
          (if inclusive then Costs.plus (Costs.minus high low) (Logic.int 1)
           else Costs.minus high low)
      in
      let iterations = Facts.declare_fresh context head "iterations" Logic.Int in
      Facts.assume context head
        Logic.(
          Operation ("<=", [ int 0; iterations ])
          &&& Operation ("<=", [ iterations; Costs.at_least_zero count ]));
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
                    Operation ("<=", [ int 0; Symbol position ])
                    &&& Operation ("<", [ Symbol position; iterations ])
                    ==> equal yielded_index (Operation ("+", [ low; Symbol position ]))) ))
       | None -> ());
      Option.iter
        (fun _ ->
          declare_elements_so_far context head ~element ~collection:for_loop.collection
            ~count:iterations before element_at)
        for_loop.element_call;
      let index = Costs.plus low iterations in
      let head =
        enter_loop_head context
          (at_index { head with yielded = Some before } index)
          costs ~iterations:(Some iterations)
      in
      assume_invariants context head clauses;
      let keeps_count (at : State.frame) =
        Option.map (fun count_of -> Logic.equal (count_of at) high) for_loop.invariant_count
      in
      Option.iter (Facts.assume context head) (keeps_count { head with makes_obligations = false });
      let inside = Facts.restrict head (Logic.Operation ("<", [ iterations; count ])) in
      let through =
        Intrinsics.append_part context inside element before
          (if over_positions then
             match element_at { inside with makes_obligations = false } index with
             | Some lent -> lent
             | None -> Facts.arrive context inside "element" element
           else index)
      in
      let inside = { inside with yielded = outer_yielded } in
      let inside = Operations.spend context inside make_step_cost in
      let ends, breaks = for_loop.run_body inside index in
      let with_through (exit_frame : State.frame) =
        at_index { exit_frame with yielded = Some through } (Costs.plus index (Logic.int 1))
      in
      end_iterations context frame for_loop.for_at clauses start ~head ~inside ~ends ~breaks
        ~with_through;
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
            (keeps_count end_))
        ends;
      let most = [ Costs.at_least_zero count ] in
      let exit_ =
        exit_loop context
          (Facts.restrict head (Logic.Operation (">=", [ iterations; count ])))
          costs ~iterations:(Some iterations) ~most
      in
      let left =
        List.map
          (fun (exit_frame : State.frame) ->
            exit_loop context (with_through exit_frame) costs
              ~iterations:(Some (Costs.plus iterations (Logic.int 1)))
              ~most)
          breaks
      in
      leave_loop context frame
        (List.map
           (fun (exit_frame : State.frame) -> { exit_frame with yielded = outer_yielded })
           (exit_ :: left))
  | Over_cursor { cursor; cursor_type; next } ->
      own_cursor_loop ~for_loop context frame cursor next ~cursor_type

let run_while_loop context (frame : State.frame) (loop : while_loop) =
  let clauses = loop.while_clauses in
  let location = Facts.locate context frame.source loop.while_at in
  check_invariants context frame clauses ~when_:"on entry to the loop";
  let { loop_costs = costs; fresh_mark = mark; facts_mark; preserved; havocked = head } =
    enter_loop context frame ~entry:frame clauses ~changed:loop.changed
  in
  let head = loop.bind_parts head in
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
    | None, Some (comparison, operands) -> (
        let left, right = Validity.without_costs context (fun () -> operands at) in
        let distance from into = Logic.Operation ("-", [ into; from ]) in
        let through distance = Logic.Operation ("+", [ distance; Logic.int 1 ]) in
        match (comparison : Core.comparison) with
        | Less -> Some [ distance left right ]
        | Less_equal -> Some [ through (distance left right) ]
        | Greater -> Some [ distance right left ]
        | Greater_equal -> Some [ through (distance right left) ]
        | Equal | Not_equal -> None)
    | None, None -> None
  in
  let start_measures = if context.terminates then measure_terms inside else None in
  if context.terminates && start_measures = None then
    Facts.oblige context inside Termination location
      [ Text "This loop may not end: give it a `decreases` clause." ]
      (Logic.Boolean false);
  let most =
    match (start_measures, measure_terms frame, iterations) with
    | Some [ at_head ], Some [ on_entry ], Some iterations ->
        let last = Facts.declare_fresh context head "last" Logic.Int in
        Facts.assume context head
          Logic.(
            equal iterations (int 0)
            ==> Operation ("<=", [ at_head; on_entry ])
            &&& (Operation (">=", [ iterations; int 1 ])
                ==> (Operation ("<=", [ int 0; last ])
                    &&& Operation
                          ( "<=",
                            [
                              Operation ("+", [ Operation ("-", [ iterations; int 1 ]); last ]);
                              on_entry;
                            ] )
                    &&& Operation ("<", [ at_head; last ]))));
        [ Costs.at_least_zero (Costs.plus on_entry (Logic.int 1)) ]
    | _ -> []
  in
  check_loop_iterations context loop.while_at head costs ~mark
    ~facts:(Lambdas.list_facts_since context facts_mark @ [ inside.condition ])
    ~ends ~breaks;
  List.iter
    (fun (end_ : State.frame) ->
      check_invariants context end_ clauses ~when_:"after an iteration";
      check_preserved_validity context end_ location preserved;
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
          (exit_loop context
             (Facts.restrict at_condition (Logic.not_ holds))
             costs ~iterations ~most))
  in
  Facts.join_frames context
    (Option.to_list failing
    @ List.map
        (fun (leaving : State.frame) ->
          exit_loop context leaving costs
            ~iterations:(Option.map (fun count -> Costs.plus count (Logic.int 1)) iterations)
            ~most)
        breaks)
