let is_borrow_of_root (root : Place.root) (view : Actions.view) =
  match view with Borrow_of place -> place.root = root | Copy_of_view_in _ -> false

let lifetime_ends_at_return (context : Context.context) (view : Actions.view) =
  let place = Actions.extract_viewed_place view in
  match place.root with
  | Constant _ -> false
  | Temporary _ | Environment -> true
  | Local local ->
      if local = Self || List.mem local context.parameters then
        Context.classify_binding_mode context place.root = Own && is_borrow_of_root place.root view
      else true

let outlives_function context (place : Place.t) =
  Context.classify_binding_mode context place.root = Mut
  &&
  match place.root with
  | Local local -> List.mem local context.parameters
  | Temporary _ | Constant _ | Environment -> false

type here = {
  views : Dataflow.held_views;
  loans : Actions.loan list;
  is_live_after : Core.local -> bool;
  origin : Core.origin;
}

let find_loan context ~(at : Core.origin) (loan : Actions.loan) ~is_through_view (place : Place.t)
    ~verb : Catalog.Ownership.loan =
  {
    at;
    place = Context.find_place context place;
    is_mut = loan.mode = Mut;
    lender =
      (match loan.duration with
      | Loop_body -> Loop
      | Provide_body -> Provide_block
      | Rest_of_statement -> Rest_of_statement
      | Operand_evaluation -> Earlier_operand
      | Alias_scope name -> Alias (Context.find_root context (Local name)));
    through = (if is_through_view then Some (Context.find_place context loan.borrowed) else None);
    verb;
  }

let report_dangling_view (context : Context.context) at ~views ~act =
  let report viewed =
    Context.report context (Dangling_view { at; act; viewed; is_constant = context.is_constant });
    true
  in
  match
    Option.map Actions.extract_viewed_place (List.find_opt (lifetime_ends_at_return context) views)
  with
  | Some { root = Environment; _ } -> report Captured_variables
  | Some { root = Temporary _; _ } -> report Temporary_view
  | Some place -> report (View_of (Context.find_root context place.root))
  | None -> false

let check_disjoint (context : Context.context) first second ~on_overlap =
  match Place.classify_overlap first second with
  | Overlapping -> on_overlap ()
  | Maybe_disjoint (first, second) ->
      context.must_be_disjoint <- (min first second, max first second) :: context.must_be_disjoint
  | Disjoint -> ()

let check_body context (actions : Actions.t) moves =
  let states = Dataflow.forward context actions in
  let is_live_after = Moves.compute_live_after moves actions.body in
  let mir_local = Context.Local_table.create 16 in
  Array.iteri
    (fun local (info : Mir.local_info) ->
      match info.kind with
      | Source { local = core; _ } -> Context.Local_table.replace mir_local core local
      | Temporary | Lent _ -> ())
    actions.body.locals;
  let is_live_after ({ block; index } : Actions.position) core =
    match Context.Local_table.find_opt mir_local core with
    | Some local -> is_live_after block index local
    | None -> false
  in
  let resolve = Dataflow.resolve context in
  let list_viewed_places here views =
    List.map Actions.extract_viewed_place (resolve here.views views)
  in
  let check_each_step positions check_step =
    List.iter
      (fun ({ block; index } as position : Actions.position) ->
        match states.(block) with
        | Some before ->
            List.iteri
              (fun step_index (step : Actions.step) ->
                let { views; loans } : Dataflow.state = before.(index).(step_index) in
                check_step
                  {
                    views;
                    loans = List.concat_map (fun (_, loans) -> List.rev loans) loans;
                    is_live_after = is_live_after position;
                    origin = step.origin;
                  }
                  step)
              actions.steps.(block).(index)
        | None -> ())
      positions
  in
  let all_positions =
    List.concat
      (List.mapi
         (fun block positions ->
           List.init (Array.length positions) (fun index : Actions.position -> { block; index }))
         (Array.to_list actions.steps))
  in
  let list_covering_loans (here : here) (place : Place.t) =
    List.filter_map
      (fun (loan : Actions.loan) ->
        if Place.classify_overlap loan.borrowed place <> Disjoint then Some (loan, false)
        else if
          List.exists
            (fun viewed -> Place.classify_overlap viewed place <> Disjoint)
            (list_viewed_places here [ Borrow_of loan.borrowed ])
        then Some (loan, true)
        else None)
      here.loans
  in
  let is_mut ((loan : Actions.loan), _) = loan.mode = Mut in
  let reported_owners = Hashtbl.create 4 in
  let check_use (here : here) (place : Place.t) =
    match List.find_opt is_mut (list_covering_loans here place) with
    | Some (loan, is_through_view) ->
        Context.report context
          (Conflicting_loan
             (find_loan context ~at:here.origin loan ~is_through_view place ~verb:Be_used))
    | None -> ()
  in
  let check_mutation (here : here) (place : Place.t) ~verb =
    let at = here.origin in
    let covering = list_covering_loans here place in
    match (List.find_opt is_mut covering, covering) with
    | Some (loan, is_through_view), _ ->
        Context.report context
          (Conflicting_loan (find_loan context ~at loan ~is_through_view place ~verb))
    | None, (loan, is_through_view) :: _ ->
        Context.report context
          (Mutated_while_lent (find_loan context ~at loan ~is_through_view place ~verb))
    | None, [] ->
        List.iter
          (fun ((holder : Place.root), viewed) ->
            let in_use =
              match holder with
              | Local local when not (outlives_function context { root = holder; steps = [] }) ->
                  here.is_live_after local
              | Local _ | Temporary _ | Constant _ | Environment -> true
            in
            if
              in_use
              && List.exists
                   (fun view ->
                     Place.classify_overlap (Actions.extract_viewed_place view) place <> Disjoint)
                   viewed
            then
              Context.report context
                (Mutated_while_viewed
                   {
                     at;
                     place = Context.find_place context place;
                     verb;
                     holder = Context.find_root context holder;
                   }))
          here.views
  in
  check_each_step all_positions (fun here (step : Actions.step) ->
      let at = here.origin in
      match step.action with
      | Read place -> check_use here place
      | Mutate place ->
          check_use here place;
          check_mutation here place ~verb:Be_passed_mut
      | Assign place -> check_mutation here place ~verb:Be_assigned
      | Move { place; type_; is_returned; is_captured } -> (
          check_use here place;
          match
            Move_rules.decide_move context place ~origin:here.origin ~type_ ~is_returned
              ~is_captured
          with
          | Moves -> check_mutation here place ~verb:Be_moved
          | Reads -> ()
          | Refused refuse -> refuse context at type_)
      | Move_out_of_lent type_ ->
          Context.report context
            (Moved_out_of_lent { at; copy = Context.find_copy context type_ here.origin })
      | Arguments { borrowed_arguments; view_arguments; is_yielded } ->
          List.iteri
            (fun first_index (first : Actions.borrowed_argument) ->
              List.iteri
                (fun second_index (second : Actions.borrowed_argument) ->
                  if second_index > first_index && (first.mode = Mut || second.mode = Mut) then
                    check_disjoint context first.place second.place ~on_overlap:(fun () ->
                        let exclusive, also =
                          if first.mode = Mut then (first, second) else (second, first)
                        in
                        Context.report context
                          (Arguments_overlap
                             {
                               at = Context.cover_with_mode_keyword context second.origin;
                               exclusive = Context.find_place context exclusive.place;
                               also = Context.find_place context also.place;
                               call = here.origin;
                               is_yielded;
                             })))
                borrowed_arguments)
            borrowed_arguments;
          List.iter
            (fun (argument : Actions.view_argument) ->
              let viewed = list_viewed_places here argument.views in
              List.iter
                (fun (passed : Actions.borrowed_argument) ->
                  if passed.position <> argument.position && passed.mode = Mut then
                    List.iter
                      (fun viewed_place ->
                        check_disjoint context viewed_place passed.place ~on_overlap:(fun () ->
                            Context.report context
                              (View_argument_overlap
                                 {
                                   at = Context.cover_with_mode_keyword context argument.origin;
                                   passed = Context.find_place context passed.place;
                                   call = here.origin;
                                 })))
                      viewed)
                borrowed_arguments)
            view_arguments
      | Drop dropped ->
          List.iter
            (fun (dropped : Actions.dropped_owner) ->
              let views_owner ((holder : Place.root), viewed) =
                (match holder with
                  | Local local ->
                      here.is_live_after local
                      && not (outlives_function context { root = holder; steps = [] })
                  | Temporary _ | Constant _ | Environment -> false)
                && List.exists (is_borrow_of_root dropped.owner) viewed
              in
              match List.find_opt views_owner here.views with
              | Some (holder, _) when not (Hashtbl.mem reported_owners dropped.origin) -> (
                  Hashtbl.replace reported_owners dropped.origin ();
                  let holder =
                    match holder with
                    | Local local -> Context.Local_table.find_opt context.names local
                    | _ -> None
                  in
                  match dropped.owner with
                  | Temporary _ ->
                      Context.report context
                        (Temporary_dropped_while_viewed { at = dropped.origin; holder })
                  | Local _ | Constant _ | Environment ->
                      Context.report context
                        (Dropped_while_viewed
                           {
                             at = dropped.origin;
                             owner = Context.find_root context dropped.owner;
                             holder;
                           }))
              | _ -> ())
            dropped
      | Bind_lent_part { scrutinee; lent_part_type } ->
          Context.report context
            (Lent_part_bound { at; copy = Context.find_copy context lent_part_type scrutinee })
      | Pass_owned_function views -> (
          match
            List.find_opt
              (fun (viewed : Place.t) ->
                match viewed.root with
                | Environment -> true
                | Temporary _ | Constant _ -> false
                | Local _ -> Context.classify_binding_mode context viewed.root <> Own)
              (list_viewed_places here views)
          with
          | Some { root = Environment; _ } ->
              Context.report context (Capturing_lambda_stored { at })
          | Some viewed ->
              Context.report context
                (Unowned_function_stored { at; viewed = Context.find_place context viewed })
          | None -> ())
      | Return_view views ->
          let views = resolve here.views views in
          if
            (not
               (report_dangling_view context at ~views
                  ~act:(if context.is_constant then Is else Returns)))
            && context.implements_capability
            && List.exists (is_borrow_of_root (Local Self)) views
          then Context.report context (Returned_view_of_implementation { at })
      | Store { place; views; _ } -> (
          if outlives_function context place then
            let resolved = resolve here.views views in
            let views_borrowed_parameter (view : Actions.view) =
              match (Actions.extract_viewed_place view).root with
              | Local local when local = Self || List.mem local context.parameters -> (
                  match Context.Local_table.find_opt context.types local with
                  | Some type_ -> not (Context.is_view context type_)
                  | None -> false)
              | Local _ | Temporary _ | Constant _ | Environment -> false
            in
            let stores_argument_view (view : Actions.view) =
              context.implements_capability && place.root = Local Self
              &&
              match (Actions.extract_viewed_place view).root with
              | Local local -> local <> Self && List.mem local context.parameters
              | Temporary _ | Constant _ | Environment -> false
            in
            if
              not
                (report_dangling_view context at ~views:resolved
                   ~act:(Stores_in (Context.find_root context place.root)))
            then
              match
                ( List.find_opt stores_argument_view resolved,
                  List.exists (is_borrow_of_root place.root) resolved,
                  List.find_opt views_borrowed_parameter resolved )
              with
              | Some stored_view, _, _ ->
                  Context.report context
                    (Stored_view_in_implementation
                       {
                         at;
                         viewed =
                           Context.find_root context (Actions.extract_viewed_place stored_view).root;
                       })
              | None, true, _ ->
                  Context.report context
                    (Self_referential_store { at; root = Context.find_root context place.root })
              | None, false, Some parameter_view ->
                  let parameter = (Actions.extract_viewed_place parameter_view).root in
                  Context.report context
                    (Stored_view_of_borrowed
                       {
                         at;
                         parameter = Context.find_root context parameter;
                         holder = Context.find_root context place.root;
                         declaration = Context.find_view_declaration context parameter;
                       })
              | None, false, None -> ())
      | Yield_point { views; parts; forwarded } -> (
          let forwarded = resolve here.views forwarded in
          let is_dangling =
            report_dangling_view context at ~views:(resolve here.views views @ forwarded) ~act:Lends
          in
          let owned =
            List.find_opt
              (fun (part : Place.t) ->
                part.steps <> [] && Context.classify_binding_mode context part.root = Own)
              parts
          in
          let receiver =
            match List.rev context.parameters with first :: _ -> Some first | [] -> None
          in
          let other_parameter =
            List.find_map
              (fun (part : Place.t) ->
                match part.root with
                | Local local
                  when (local = Self || List.mem local context.parameters)
                       && Some local <> receiver
                       && Context.classify_binding_mode context part.root <> Own ->
                    Some part.root
                | _ -> None)
              (parts @ List.map Actions.extract_viewed_place forwarded)
          in
          match (owned, other_parameter) with
          | Some part, _ when not is_dangling ->
              Context.report context
                (Lent_owned_part { at; part = Context.find_root context part.root })
          | None, Some root when not is_dangling ->
              Context.report context
                (Lent_other_parameter { at; root = Context.find_root context root })
          | _ -> ())
      | Bind _ | Bind_views _ | Start_loan _ | End_loans _ -> ());
  let list_effects positions =
    let mutations = ref [] and uses = ref [] in
    check_each_step positions (fun here (step : Actions.step) ->
        let list_viewed place = list_viewed_places here [ Copy_of_view_in place ] in
        match step.action with
        | Read place -> uses := (place :: list_viewed place) @ !uses
        | Mutate place ->
            uses := (place :: list_viewed place) @ !uses;
            mutations := (place, here.origin) :: !mutations
        | Assign place -> mutations := (place, here.origin) :: !mutations
        | Move { place; type_; is_returned; is_captured } -> (
            uses := place :: !uses;
            match
              Move_rules.decide_move context place ~origin:here.origin ~type_ ~is_returned
                ~is_captured
            with
            | Moves -> mutations := (place, here.origin) :: !mutations
            | Reads | Refused _ -> ())
        | Move_out_of_lent _ | Bind _ | Yield_point _ | Bind_views _ | Store _ | Return_view _
        | Drop _ | Bind_lent_part _ | Pass_owned_function _ | Start_loan _ | End_loans _
        | Arguments _ ->
            ());
    (!mutations, !uses)
  in
  List.iter
    (fun ({ schedule; branches } : Actions.fork_join_block) ->
      let branches = List.map list_effects branches in
      List.iteri
        (fun index (mutations, _) ->
          List.iteri
            (fun other (other_mutations, other_uses) ->
              if other <> index then
                let used = other_uses @ List.map fst other_mutations in
                List.iter
                  (fun (place, origin) ->
                    List.iter
                      (fun used_place ->
                        check_disjoint context place used_place ~on_overlap:(fun () ->
                            Context.report context
                              (Branch_data_race
                                 { at = origin; schedule; place = Context.find_place context place })))
                      used)
                  mutations)
            branches)
        branches)
    actions.fork_join_blocks;
  List.iter
    (fun ({ schedule; body; pattern_locals; temporaries } : Actions.fork_join_loop) ->
      let iteration_locals = ref pattern_locals in
      check_each_step body (fun _ (step : Actions.step) ->
          match step.action with
          | Bind locals -> iteration_locals := locals @ !iteration_locals
          | _ -> ());
      List.iter
        (fun ((place : Place.t), origin) ->
          let is_outside_iteration =
            match place.root with
            | Constant _ | Environment | Local Self -> true
            | Local local -> not (List.mem local !iteration_locals)
            | Temporary local -> not (List.mem local temporaries)
          in
          if is_outside_iteration then
            Context.report context (Iteration_data_race { at = origin; schedule }))
        (fst (list_effects body)))
    actions.fork_join_loops

let check context ~read_moves ~returns_to_caller (mir : Mir.Graph.t) =
  let check_one body ~returns_to_caller =
    let moves = read_moves body in
    check_body context (Actions.of_body context moves body ~returns_to_caller) moves
  in
  check_one mir.body ~returns_to_caller;
  Array.iter (check_one ~returns_to_caller:false) mir.lambdas
