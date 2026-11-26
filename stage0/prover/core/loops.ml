type received = {
  has_another : Logic.term;
  element : Logic.term;
  through : Logic.term;
  advance : State.frame -> State.frame;
}

type loop_start = {
  costs : Loop_costs.t;
  preserved :
    (Catalog.Prover.value * Types.ty * Logic.term * (State.frame -> Logic.term option)) list;
  havocked : State.frame;
}

type while_loop = {
  while_at : Core.origin;
  while_clauses : Mir.loop_clause list;
  changed : State.changed_part list;
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
  compute_changed_in : State.frame -> State.changed_part list;
  compute_changed_by_body : State.frame -> State.changed_part list;
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

let havoc context frame (changed : State.changed_part list) =
  List.fold_left
    (fun (frame : State.frame) (part : State.changed_part) ->
      let held =
        match part.root with
        | Core_local Self -> Option.map (fun whole -> (frame.self_type, whole)) frame.self
        | root ->
            Option.map
              (fun whole -> (Encoding.find_local_type context frame root, whole))
              (Locals.find_opt root frame.locals)
      in
      match held with
      | None -> frame
      | Some (None, _) -> Facts.raise_bug "a loop changes a local that has a value and no type"
      | Some (Some ty, whole) -> (
          match
            Encoding.replace_part context ty whole part.fields (fun part_type _ ->
                Encoding.arrive context frame "loop" part_type)
          with
          | None ->
              Facts.raise_bug "a loop changes a field of `%s`, whose fields the prover cannot see"
                (Types.show ty)
          | Some term -> (
              match part.root with
              | Core_local Self -> { frame with self = Some term }
              | root -> { frame with locals = Locals.add root term frame.locals })))
    frame changed

let list_validity_obligations context (entry : State.frame) (changed : State.changed_part list) =
  List.filter_map
    (fun root ->
      match Encoding.find_root context entry root with
      | Some (ty, before) -> (
          match Validity.make_validity context entry ~assuming:false ~deep:true ty before with
          | Logic.Boolean true -> None
          | valid ->
              Some
                ( Facts.describe_local context entry root,
                  ty,
                  valid,
                  fun (at : State.frame) -> Option.map snd (Encoding.find_root context at root) ))
      | None -> None)
    (List.sort_uniq compare (List.map (fun (part : State.changed_part) -> part.root) changed))

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
          Obligations.oblige context end_ location
            (Preserved_invariant { type_ = ty; value = described })
            (Logic.( ==> ) valid_on_entry
               (Validity.make_validity context end_ ~assuming:false ~deep:true ty term))
      | None -> ())
    preserved

let check_loop_clauses context frame clauses ~moment =
  List.iter
    (fun (clause : Mir.loop_clause) ->
      match clause with
      | Invariant invariant ->
          let _, term =
            Obligations.with_condition context invariant.holds_when (fun () ->
                Validity.read_specification context frame invariant)
          in
          Obligations.oblige ~holds_when:invariant.holds_when context frame
            (Facts.locate context frame.source invariant.origin)
            (Loop_invariant { clause = Facts.quote frame.source invariant.origin; moment })
            term
      | Decreases measures ->
          List.iter
            (fun (measure : Mir.formula) ->
              Validity.check_defined context frame ~holds_when:measure.holds_when measure)
            measures
      | Cost _ -> ())
    clauses

let assume_invariants context frame clauses =
  List.iter
    (fun (invariant : Mir.formula) ->
      let _, term =
        Validity.read_specification context { frame with makes_obligations = false } invariant
      in
      Facts.assume context frame term)
    (Validity.list_invariants clauses)

let enter_loop ?holds context frame ~entry clauses ~changed =
  let holds = Option.value holds ~default:changed in
  let costs = Loop_costs.enter context frame ~entry clauses ~holds ~changed in
  let preserved = list_validity_obligations context frame changed in
  let head = havoc context frame changed in
  assume_preserved_validity context head preserved;
  { costs; preserved; havocked = head }

let end_scope ~(outer : State.frame) (frame : State.frame) =
  { frame with locals = Locals.filter (fun id _ -> Locals.mem id outer.locals) frame.locals }

let leave_loop context frame frames =
  Option.map (end_scope ~outer:frame) (Joins.join_frames context frames)

let end_iterations context (frame : State.frame) loop_at clauses measure (start : loop_start) ~head
    ~(inside : State.frame) ~iterations ~iteration_bounds ~ends ~breaks ~with_through =
  let location = Facts.locate context frame.source loop_at in
  Loop_costs.check_iterations context loop_at head start.costs ~iterations ~iteration_bounds ~inside
    ~ends:(List.map with_through ends) ~breaks:(List.map with_through breaks);
  List.iter
    (fun (end_ : State.frame) ->
      let through = with_through end_ in
      check_loop_clauses context through clauses ~moment:After_iteration;
      check_preserved_validity context end_ location start.preserved;
      Termination.check_loop_measure context through location measure)
    ends

let declare_elements_so_far context (head : State.frame) ~element ~collection ~count visited
    find_element_at =
  let symbol = Facts.make_fresh_name context "position" in
  let position = Logic.Symbol symbol in
  let premise = Logic.(less_equal (int 0) position &&& less position count) in
  (match Models.index_sequence context element visited position with
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
        (Values.assume_extensional context head (Models.make_sequence_type element) visited)
        (Models.find_model context
           (Encoding.substitute_type context head collection_type)
           collected ~element)
  | None -> ()

let prove_receiving_loop ~most ~(for_loop : for_loop) context frame ~element_type ~changed ~holds
    ~start ~receive =
  let clauses = for_loop.for_clauses in
  let entry =
    { frame with State.visited = Some (Intrinsics.make_empty_sequence context frame element_type) }
  in
  check_loop_clauses context entry clauses ~moment:On_entry;
  let loop = enter_loop ~holds context frame ~entry clauses ~changed in
  let costs = loop.costs and head = for_loop.bind_parts loop.havocked in
  let before = start head in
  let iterations = Models.make_sequence_length context element_type before in
  let head =
    Loop_costs.enter_head context
      { head with visited = Some before }
      costs ~iterations:(Some iterations)
  in
  assume_invariants context head clauses;
  let ended_mark = Query.count_facts context.query in
  let received = receive head before in
  let through = received.through in
  let inside = received.advance (Facts.restrict head received.has_another) in
  let inside = { (Loop_costs.spend_step context inside) with visited = frame.visited } in
  let ends, breaks = for_loop.run_body inside received.element in
  let with_through (exit_frame : State.frame) = { exit_frame with visited = Some through } in
  end_iterations context frame for_loop.for_at clauses
    (Termination.read_loop_measure context clauses ~head)
    loop ~head ~inside ~iterations:(Some iterations) ~iteration_bounds:most ~ends ~breaks
    ~with_through;
  let ended = received.advance (Facts.restrict head (Logic.not_ received.has_another)) in
  let exit_ =
    Loop_costs.leave_counted context ~clause_at:head
      { ended with visited = Some before }
      costs ~iterations:(Some iterations) ~most ~count:iterations ~since:ended_mark
  in
  let left =
    List.map
      (fun (exit_frame : State.frame) ->
        let left_at = with_through exit_frame in
        Loop_costs.leave_counted context ~clause_at:left_at left_at costs
          ~iterations:(Some (Logic.add iterations (Logic.int 1)))
          ~most
          ~count:(Models.make_sequence_length context element_type through)
          ~since:ended_mark)
      breaks
  in
  leave_loop context frame
    (List.map
       (fun (exit_frame : State.frame) -> { exit_frame with visited = frame.visited })
       (exit_ :: left))

let cursor_trait : Path.t = Well_known.make_path Cursor

let declare_visited context frame element =
  let visited =
    Facts.declare_fresh context frame "parts"
      (Encoding.declare_sort context (Models.make_sequence_type element))
  in
  Facts.assume context frame
    Logic.(greater_equal (Models.make_sequence_length context element visited) (int 0));
  visited

let names_visited (clauses : Mir.loop_clause list) =
  List.exists
    (function
      | Mir.Invariant invariant -> Contracts.mentions_visited invariant
      | Decreases measures -> List.exists Contracts.mentions_visited measures
      | Cost { bound = Order_of bound | At_most bound | Exactly bound; _ } ->
          Contracts.mentions_visited bound)
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
      Models.index_sequence context element entry_model (Logic.add (length visited) index) )
  with
  | Some visited_value, Some entry_value, Some remaining_value, Some entry_value_ahead ->
      Facts.assume context head
        Logic.(
          equal (add (length visited) (length model)) (length entry_model)
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
      Models.index_sequence context element model (Logic.add index (Logic.int 1)) )
  with
  | Some first, Some value_after, Some value_ahead ->
      Obligations.oblige context after location Visited_out_of_order
        Logic.(
          has_another
          ==> (greater (length model) (int 0)
              &&& equal pulled first
              &&& equal (add (length model_after) (int 1)) (length model)
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
  let element_type = Encoding.substitute_type context frame for_loop.element_type in
  let find_model (at : State.frame) =
    if names_visited clauses then
      Models.find_model context
        (Encoding.substitute_type context frame cursor_type)
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
  let self_type = Encoding.substitute_type context frame cursor_type in
  let self_binding =
    Types.bind_argument
      (Types.make_self_parameter cursor_trait)
      (Types.Type cursor_type) Types.no_substitution
  in
  let path, callee_substitution =
    match evidence with
    | Impl { impl; substitution } | Derived_for_view { viewed = impl; substitution } ->
        ( Well_known.make_impl_method_path Cursor_next ~impl,
          Types.combine_substitutions substitution self_binding )
    | Bound -> (Well_known.make_method_path Cursor_next, self_binding)
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
    | None -> Facts.raise_unsupported location (Unreadable_cursor cursor_type)
  in
  let option_type =
    Types.Named { path = Well_known.make_path Option; arguments = [ Types.Type element_type ] }
  in
  let pulling : Invocation.site = { origin = next_origin; type_ = option_type } in
  let measures = Termination.find_written_measures clauses in
  Termination.require_measure context ~loop:"a loop over a cursor"
    ~is_measured:(Option.is_some measures);
  let find_measured (at : State.frame) =
    Option.map (Termination.read_measures context at) measures
  in
  let entry_measure = match find_measured frame with Some [ entry ] -> Some entry | _ -> None in
  let next_costs =
    List.concat_map
      (fun (next_clauses : State.clauses) -> next_clauses.costs)
      (Contracts.list_declared_clauses contract)
  in
  let states_only_amortized_cost =
    List.exists
      (fun (cost : Mir.cost) ->
        cost.amortized
        && not
             (List.exists
                (fun (other : Mir.cost) -> (not other.amortized) && other.resource = cost.resource)
                next_costs))
      next_costs
  in
  let holds =
    if states_only_amortized_cost then for_loop.compute_changed_in frame
    else for_loop.compute_changed_by_body frame
  in
  prove_receiving_loop ~for_loop context frame ~element_type
    ~changed:(for_loop.compute_changed_in frame)
    ~holds ~most:(Option.to_list entry_measure)
    ~start:(fun head ->
      let before = declare_visited context head element_type in
      (match (entry_measure, find_measured head) with
      | Some entry, Some [ now ] ->
          Facts.assume context head
            Logic.(
              less_equal (add (Models.make_sequence_length context element_type before) now) entry
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
      let recursive_callee = Termination.find_recursive_callee context head location next.callee in
      let ({ frame = after; result = pulled; _ } : Calls.applied) =
        Calls.call_contract ~recursive_callee context head pulling next path contract
          [
            {
              position = 0;
              mode = Language.Mode.Mut;
              shape = Other;
              origin = None;
              passed_place = Some cursor_access;
              is_step_self = false;
              type_ = cursor_type;
              declared_type = cursor_type;
              term = cursor;
            };
          ]
          ~substitution_of:(fun _ -> callee_substitution)
          ~type_arguments:[ Types.Type cursor_type ]
      in
      let some_variant = Some (Well_known.show_variant Option_some) in
      let has_another =
        Logic.Is (Encoding.make_constructor_symbol option_type some_variant, pulled)
      in
      let element =
        Logic.Apply
          ( Encoding.make_selector_symbol option_type some_variant
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
        through = Intrinsics.append_element context inside element_type before element;
        advance =
          (fun (frame : State.frame) ->
            let now = cursor_access.read after in
            let advanced, end_write = cursor_access.write frame ~is_valid:true now in
            end_write advanced;
            { advanced with spent = after.spent });
      })

let run_for_loop context frame (for_loop : for_loop) =
  let clauses = for_loop.for_clauses in
  match for_loop.iterable with
  | Over_range { low; high; inclusive } ->
      let element =
        Encoding.substitute_type context frame
          (Option.value for_loop.lent_element ~default:for_loop.element_type)
      in
      let over_positions = Option.is_some for_loop.lent_element in
      let find_element_at (at : State.frame) position =
        Option.map
          (fun element_of -> element_of (for_loop.bind_element at position))
          for_loop.element_call
      in
      let outer_visited = frame.visited in
      let bind_at_index (exit_frame : State.frame) next = for_loop.bind_element exit_frame next in
      let entry =
        bind_at_index
          { frame with visited = Some (Intrinsics.make_empty_sequence context frame element) }
          low
      in
      check_loop_clauses context entry clauses ~moment:On_entry;
      let start =
        enter_loop context frame ~entry clauses ~changed:(for_loop.compute_changed_in frame)
      in
      let costs = start.costs and head = for_loop.bind_parts start.havocked in
      let count =
        Logic.normalize_linear
          (if inclusive then Logic.add (Logic.subtract high low) (Logic.int 1)
           else Logic.subtract high low)
      in
      let iterations = Facts.declare_fresh context head "iterations" Logic.Int in
      Facts.assume context head
        Logic.(less_equal (int 0) iterations &&& less_equal iterations (at_least_zero count));
      let before = declare_visited context head element in
      Facts.assume context head
        (Logic.equal (Models.make_sequence_length context element before) iterations);
      (let position = Facts.make_fresh_name context "index" in
       match
         if over_positions then None
         else Models.index_sequence context element before (Logic.Symbol position)
       with
       | Some visited_index ->
           Facts.assume context head
             (Logic.forall
                ( [ (position, Logic.Int) ],
                  Logic.(
                    less_equal (int 0) (Symbol position)
                    &&& less (Symbol position) iterations
                    ==> equal visited_index (add low (Symbol position))) ))
       | None -> ());
      Option.iter
        (fun _ ->
          declare_elements_so_far context head ~element ~collection:for_loop.collection
            ~count:iterations before find_element_at)
        for_loop.element_call;
      let index = Logic.add low iterations in
      let head =
        Loop_costs.enter_head context
          (bind_at_index { head with visited = Some before } index)
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
        Intrinsics.append_element context inside element before
          (if over_positions then
             match find_element_at { inside with makes_obligations = false } index with
             | Some lent -> lent
             | None -> Encoding.arrive context inside "element" element
           else index)
      in
      let inside = { inside with visited = outer_visited } in
      let inside = Loop_costs.spend_step context inside in
      let ends, breaks = for_loop.run_body inside index in
      let with_through (exit_frame : State.frame) =
        bind_at_index { exit_frame with visited = Some through } (Logic.add index (Logic.int 1))
      in
      end_iterations context frame for_loop.for_at clauses
        (Termination.read_loop_measure context clauses ~head)
        start ~head ~inside ~iterations:(Some iterations) ~iteration_bounds:[ count ] ~ends ~breaks
        ~with_through;
      List.iter
        (fun (end_ : State.frame) ->
          Option.iter
            (Obligations.oblige context end_
               (Facts.locate context frame.source for_loop.for_at)
               Element_count_changes)
            (find_kept_count end_))
        ends;
      let most = [ Logic.at_least_zero count ] in
      let exit_ =
        Loop_costs.leave context ~clause_at:head
          (Facts.restrict head (Logic.greater_equal iterations count))
          costs ~iterations:(Some iterations) ~most
      in
      let left =
        List.map
          (fun (exit_frame : State.frame) ->
            let left_at = with_through exit_frame in
            Loop_costs.leave context ~clause_at:left_at left_at costs
              ~iterations:(Some (Logic.add iterations (Logic.int 1)))
              ~most)
          breaks
      in
      leave_loop context frame
        (List.map
           (fun (exit_frame : State.frame) -> { exit_frame with visited = outer_visited })
           (exit_ :: left))
  | Over_cursor { cursor; cursor_type; next; next_origin } ->
      prove_cursor_loop ~for_loop context frame cursor next ~cursor_type ~next_origin

let run_while_loop context (frame : State.frame) (loop : while_loop) =
  let clauses = loop.while_clauses in
  check_loop_clauses context frame clauses ~moment:On_entry;
  let start = enter_loop context frame ~entry:frame clauses ~changed:loop.changed in
  let costs = start.costs and head = loop.bind_parts start.havocked in
  let iterations = Loop_costs.declare_iterations context head costs in
  let head = Loop_costs.enter_head context head costs ~iterations in
  assume_invariants context head clauses;
  let tested = loop.test head in
  let entered =
    Option.map
      (fun (at_condition, holds) ->
        Loop_costs.spend_step context (Facts.restrict at_condition holds))
      tested
  in
  let ends, breaks =
    match entered with Some entered -> loop.run_body entered | None -> ([], [])
  in
  let inside =
    match entered with Some entered -> entered | None -> Facts.restrict head (Logic.Boolean false)
  in
  let measure =
    Termination.read_loop_measure
      ?implicit:(Termination.make_comparison_measure context loop.measure_operands)
      context clauses ~head
  in
  Termination.require_measure context ~loop:"a `while` loop" ~is_measured:(Option.is_some measure);
  let iteration_bounds =
    match
      ( Option.map
          (fun (measure : Termination.loop_measure) -> (measure.at_head, measure.read frame))
          measure,
        iterations )
    with
    | Some ([ at_head ], [ on_entry ]), Some iterations ->
        let last = Facts.declare_fresh context head "last" Logic.Int in
        Facts.assume context head
          Logic.(
            equal iterations (int 0)
            ==> less_equal at_head on_entry
            &&& (greater_equal iterations (int 1)
                ==> (less_equal (int 0) last
                    &&& less_equal (add (subtract iterations (int 1)) last) on_entry
                    &&& less at_head last)));
        [ Logic.add on_entry (Logic.int 1) ]
    | _ -> []
  in
  let most = List.map Logic.at_least_zero iteration_bounds in
  end_iterations context frame loop.while_at clauses measure start ~head ~inside ~iterations
    ~iteration_bounds ~ends ~breaks ~with_through:Fun.id;
  let failing =
    Option.bind tested (fun (at_condition, holds) ->
        loop.on_failure
          (Loop_costs.leave context ~clause_at:head
             (Facts.restrict at_condition (Logic.not_ holds))
             costs ~iterations ~most))
  in
  Joins.join_frames context
    (Option.to_list failing
    @ List.map
        (fun (leaving : State.frame) ->
          Loop_costs.leave context ~clause_at:leaving leaving costs
            ~iterations:(Option.map (fun count -> Logic.add count (Logic.int 1)) iterations)
            ~most)
        breaks)
