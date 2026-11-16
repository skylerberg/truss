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

let describe_loan context (loan : Actions.loan) ~is_through_view (place : Place.t) ~verb =
  let lender =
    match loan.duration with
    | Loop_body -> "the loop"
    | Provide_body -> "the `provide` block"
    | Rest_of_statement -> "a lending call until this statement ends"
    | Operand_evaluation -> "an earlier operand of this expression"
  and through =
    if is_through_view then
      Printf.sprintf " through `%s`, which views it" (Context.show context loan.borrowed)
    else ""
  in
  match loan.mode with
  | Mut ->
      Printf.sprintf "`%s` is lent `mut` to %s%s, so it cannot be used here."
        (Context.show context place) lender through
  | Read | Own ->
      Printf.sprintf "`%s` cannot %s while it is lent to %s%s." (Context.show context place) verb
        lender through

let report_dangling_view context at ~views ~doing ~fix =
  let report_view = Context.report context View_escapes at in
  match
    Option.map Actions.extract_viewed_place (List.find_opt (lifetime_ends_at_return context) views)
  with
  | Some { root = Environment; _ } ->
      report_view
        (Printf.sprintf
           "This %s a capturing lambda. A lambda's captured variables live in this function's \
            stack frame, so the lambda would dangle. %s"
           doing fix);
      true
  | Some { root = Temporary _; _ } ->
      report_view
        (Printf.sprintf
           "This %s a view of a temporary, which is dropped before the function returns, so the \
            view would dangle. %s"
           doing fix);
      true
  | Some place ->
      report_view
        (Printf.sprintf
           "This %s a view of `%s`, which is dropped when the function returns, so the view would \
            dangle. %s"
           doing
           (Context.show_root context place.root)
           fix);
      true
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
        Context.report context Conflicting_loan
          (Context.locate_origin context here.origin)
          (describe_loan context loan ~is_through_view place ~verb:"be used")
    | None -> ()
  in
  let check_mutation (here : here) (place : Place.t) ~verb =
    let at = Context.locate_origin context here.origin in
    let covering = list_covering_loans here place in
    match (List.find_opt is_mut covering, covering) with
    | Some (loan, is_through_view), _ ->
        Context.report context Conflicting_loan at
          (describe_loan context loan ~is_through_view place ~verb)
    | None, (loan, is_through_view) :: _ ->
        Context.report context Mutated_while_viewed at
          (describe_loan context loan ~is_through_view place ~verb)
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
              Context.report context Mutated_while_viewed at
                (Printf.sprintf "`%s` cannot %s while `%s`, which views it, is still live."
                   (Context.show context place) verb
                   (Context.show_root context holder)))
          here.views
  in
  check_each_step all_positions (fun here (step : Actions.step) ->
      let at = Context.locate_origin context here.origin in
      match step.action with
      | Read place -> check_use here place
      | Mutate place ->
          check_use here place;
          check_mutation here place ~verb:"be passed `mut`"
      | Assign place -> check_mutation here place ~verb:"be assigned"
      | Move { place; type_; is_returned; is_captured } -> (
          check_use here place;
          match
            Move_rules.decide_move context place ~origin:here.origin ~type_ ~is_returned
              ~is_captured
          with
          | Moves -> check_mutation here place ~verb:"be moved"
          | Reads -> ()
          | Refused refuse -> refuse context at type_)
      | Move_out_of_lent type_ ->
          Context.report context Not_owned at
            ~fixes:(Move_rules.copy_fix context "Copy it." type_ at)
            "This part is lent, so it cannot be moved: the loan ends when the statement ends. Copy \
             it instead."
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
                        Context.report context Conflicting_loan
                          (Context.locate_with_mode_keyword context second.origin)
                          (Printf.sprintf
                             (if is_yielded then
                                format_of_string
                                  "`%s` is lent `mut` to the yielded value, so `%s` cannot be lent \
                                   to it too."
                              else
                                "`%s` is passed `mut` to this call, so the call cannot also use \
                                 `%s`.")
                             (Context.show context exclusive.place)
                             (Context.show context also.place))))
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
                            Context.report context Conflicting_loan
                              (Context.locate_with_mode_keyword context argument.origin)
                              (Printf.sprintf
                                 "`%s` is passed `mut` to this call, so the call cannot also take \
                                  a view of it."
                                 (Context.show context passed.place))))
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
                  let named_holder =
                    match holder with
                    | Local local when Context.Local_table.mem context.names local ->
                        Some (Context.show_root context holder)
                    | _ -> None
                  in
                  let holder =
                    match named_holder with
                    | Some name -> Printf.sprintf "`%s`" name
                    | None -> "the value built here"
                  in
                  match dropped.owner with
                  | Temporary _ ->
                      Context.report context Views_temporary
                        (Context.locate_origin context dropped.origin)
                        (Printf.sprintf
                           "This temporary is dropped while %s may still store a view of it, which \
                            would dangle. Bind the temporary to a name with `let`%s, so that it \
                            outlives the view."
                           holder
                           (match named_holder with
                           | Some name -> Printf.sprintf " in the block that declares `%s`" name
                           | None -> ""))
                  | Local _ | Constant _ | Environment ->
                      Context.report context View_escapes
                        (Context.locate_origin context dropped.origin)
                        (Printf.sprintf
                           "`%s` is dropped at the end of its scope while %s may still store a \
                            view of it, which would dangle."
                           (Context.show_root context dropped.owner)
                           holder))
              | _ -> ())
            dropped
      | Bind_lent_part { lent_part; type_ } ->
          Context.report context Lent_part_escapes at
            ~fixes:
              (Move_rules.copy_fix context "Copy the lent part." type_
                 (Context.locate_origin context lent_part))
            "This part is lent only until the statement ends, so it cannot be bound to a name. Use \
             it in this statement, or copy it."
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
              Context.report context View_escapes at
                "This lambda captures local variables, and the callee may store a function that it \
                 takes through an `own` parameter, so the lambda could outlive them. Pass a \
                 function that captures nothing."
          | Some viewed ->
              Context.report context View_escapes at
                (Printf.sprintf
                   "`%s` is not owned here, so it may be a capturing lambda, and the callee may \
                    store a function that it takes through an `own` parameter. Pass a function \
                    that captures nothing."
                   (Context.show context viewed))
          | None -> ())
      | Return_view views ->
          let views = resolve here.views views in
          if
            (not
               (report_dangling_view context at ~views ~doing:"returns"
                  ~fix:"A function returns a view only of its parameters."))
            && context.implements_capability
            && List.exists (is_borrow_of_root (Local Self)) views
          then
            Context.report context View_crosses_capability at
              "This returns a view of the capability implementation's own state. The caller cannot \
               see the implementation, so nothing stops the next call from mutating that state \
               while the view is in use. Return a copy."
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
                   ~doing:
                     (Printf.sprintf "stores in `%s`, which outlives this function,"
                        (Context.show_root context place.root))
                   ~fix:"A `mut` parameter stores only views that the function receives.")
            then
              match
                ( List.find_opt stores_argument_view resolved,
                  List.exists (is_borrow_of_root place.root) resolved,
                  List.find_opt views_borrowed_parameter resolved )
              with
              | Some stored_view, _, _ ->
                  Context.report context View_crosses_capability at
                    (Printf.sprintf
                       "This stores a view of `%s` in a capability implementation. The caller \
                        cannot see the implementation, so it could mutate or drop the view's \
                        original while the implementation still stores the view. Store a copy."
                       (Context.show_root context (Actions.extract_viewed_place stored_view).root))
              | None, true, _ ->
                  Context.report context Self_referential at
                    (Printf.sprintf
                       "This stores a view of a part of `%s` in `%s` itself, which makes it \
                        self-referential. The caller does not know about the view, so it could \
                        mutate that part and invalidate the view."
                       (Context.show_root context place.root)
                       (Context.show_root context place.root))
              | None, false, Some parameter ->
                  let parameter =
                    Context.show_root context (Actions.extract_viewed_place parameter).root
                  in
                  Context.report context View_escapes at
                    (Printf.sprintf
                       "This stores a view of `%s` in `%s`, which outlives this function, but `%s` \
                        is only borrowed for the call, and the caller does not expect it to stay \
                        borrowed afterwards. Take `%s` as a view type, such as a `Slice`, to store \
                        a view of it."
                       parameter
                       (Context.show_root context place.root)
                       parameter parameter)
              | None, false, None -> ())
      | Write_through slice -> (
          let is_mutable_root (root : Place.root) =
            match root with
            | Temporary _ -> true
            | Constant _ | Environment -> false
            | Local local -> (
                match Context.classify_binding_mode context root with
                | Mut -> true
                | Own -> List.mem local context.mutable_locals
                | Read -> false)
          in
          match slice with
          | { steps = _ :: _; _ } ->
              Context.report context Read_only_view at
                (Printf.sprintf
                   "`%s` is a slice stored in a field, so it is read-only. Mutate the collection \
                    that it views instead."
                   (Context.show context slice))
          | { root = Local local; _ } when List.mem local context.parameters -> ()
          | _ -> (
              match
                List.find_opt
                  (fun (viewed : Place.t) -> viewed <> slice && not (is_mutable_root viewed.root))
                  (list_viewed_places here [ Copy_of_view_in slice ])
              with
              | Some viewed ->
                  Context.report context Read_only_view at
                    (Printf.sprintf
                       "`%s` views `%s`, which is read-only here, so `%s` cannot be written \
                        through."
                       (Context.show context slice) (Context.show context viewed)
                       (Context.show context slice))
              | None -> ()))
      | Yield_point { views; parts; forwarded } -> (
          let forwarded = resolve here.views forwarded in
          let is_dangling =
            report_dangling_view context at
              ~views:(resolve here.views views @ forwarded)
              ~doing:"lends" ~fix:"A method lends a view only of its parameters."
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
              Context.report context View_escapes at
                (Printf.sprintf
                   "This lends a part of %s, which the method owns and drops when it returns, so \
                    the part would dangle. Lend the whole value, move the part out of it and lend \
                    that, or return the part."
                   (match part.root with
                   | Temporary _ -> "a temporary"
                   | root -> Printf.sprintf "`%s`" (Context.show_root context root)))
          | None, Some root when not is_dangling ->
              Context.report context Lends_other_parameter at
                (Printf.sprintf
                   "This lends a part of `%s`, which is not the method's first parameter. A caller \
                    keeps only the first argument lent, so it could mutate or drop `%s` while the \
                    part is lent. A method lends a part of its first parameter, a copy of a \
                    `Plain` value, or a whole value that it made."
                   (Context.show_root context root) (Context.show_root context root))
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
        | Write_through place ->
            mutations :=
              List.map (fun viewed -> (viewed, here.origin)) (list_viewed place) @ !mutations
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
    (fun ({ keyword; branches } : Actions.fork_join_block) ->
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
                            Context.report context Data_race
                              (Context.locate_origin context origin)
                              (Printf.sprintf
                                 "Data race: one branch of this `%s` block mutates `%s`, and \
                                  another branch uses it."
                                 keyword (Context.show context place))))
                      used)
                  mutations)
            branches)
        branches)
    actions.fork_join_blocks;
  List.iter
    (fun ({ keyword; body; pattern_locals; temporaries } : Actions.fork_join_loop) ->
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
            Context.report context Data_race
              (Context.locate_origin context origin)
              (Printf.sprintf
                 "Data race: the iterations of a `%s for` run at the same time, so the body can \
                  mutate only its own element and its own locals."
                 keyword))
        (fst (list_effects body)))
    actions.fork_join_loops

let check context ~read_moves ~returns_to_caller (mir : Mir.Graph.t) =
  let check_one body ~returns_to_caller =
    let moves = read_moves body in
    check_body context (Actions.of_body context moves body ~returns_to_caller) moves
  in
  check_one mir.body ~returns_to_caller;
  Array.iter (check_one ~returns_to_caller:false) mir.lambdas
