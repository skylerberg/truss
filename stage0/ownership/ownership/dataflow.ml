type held_views = (Place.root * Actions.view list) list
type state = { views : held_views; loans : (int * Actions.loan list) list }

let find_views_held_by (held_views : held_views) (holder : Place.root) =
  List.assoc_opt holder held_views

let add_views (held_views : held_views) holder views : held_views =
  let known = Option.value ~default:[] (find_views_held_by held_views holder) in
  let added = List.filter (fun view -> not (List.mem view known)) views in
  (holder, known @ added) :: List.remove_assoc holder held_views

let aliases_place (context : Context.context) (root : Place.root) =
  match root with
  | Local local ->
      local <> Self
      && (not (List.mem local context.parameters))
      && Context.classify_binding_mode context root <> Own
  | Temporary _ | Constant _ | Environment -> false

let resolve context (held_views : held_views) (views : Actions.view list) : Actions.view list =
  List.concat_map
    (fun (view : Actions.view) ->
      let place = Actions.extract_viewed_place view in
      match (find_views_held_by held_views place.root, view) with
      | Some known, Copy_of_view_in _ -> known
      | Some known, Borrow_of _ when aliases_place context place.root -> known
      | Some known, Borrow_of _ -> known @ [ view ]
      | None, _ -> [ view ])
    views

let transfer context (step : Actions.step) (before : state) : state =
  match step.action with
  | Bind locals ->
      {
        before with
        views =
          List.filter
            (fun (holder, _) -> not (List.exists (fun local -> holder = Place.Local local) locals))
            before.views;
      }
  | Bind_views { locals; views } ->
      let viewed = resolve context before.views views in
      {
        before with
        views =
          List.fold_left
            (fun held_views holder ->
              (Place.Local holder, viewed) :: List.remove_assoc (Place.Local holder) held_views)
            before.views locals;
      }
  | Store { place; views; replaces_root } -> (
      let viewed = resolve context before.views views in
      if replaces_root then
        { before with views = (place.root, viewed) :: List.remove_assoc place.root before.views }
      else
        match viewed with
        | [] -> before
        | viewed -> { before with views = add_views before.views place.root viewed })
  | Start_loan { loan; loans } ->
      if List.mem_assoc loan before.loans then before
      else { before with loans = (loan, loans) :: before.loans }
  | End_loans ended ->
      { before with loans = List.filter (fun (loan, _) -> not (List.mem loan ended)) before.loans }
  | Read _ | Move _ | Move_out_of_lent _ | Mutate _ | Assign _ | Yield_point _ | Return_view _
  | Drop _ | Bind_lent_part _ | Pass_owned_function _ | Arguments _ ->
      before

let join (after : state) ~(into : state) =
  let views =
    List.filter
      (fun (holder, places) ->
        match find_views_held_by into.views holder with
        | Some known -> List.exists (fun place -> not (List.mem place known)) places
        | None -> true)
      after.views
  and loans = List.filter (fun loan -> not (List.mem loan into.loans)) after.loans in
  if views = [] && loans = [] then None
  else
    Some
      {
        views =
          List.fold_left
            (fun held_views (holder, places) -> add_views held_views holder places)
            into.views views;
        loans = into.loans @ loans;
      }

let forward context (actions : Actions.t) =
  let blocks = Array.length actions.steps in
  let entries = Array.make blocks None and pending = Queue.create () in
  if blocks > 0 then begin
    entries.(0) <- Some { views = []; loans = [] };
    Queue.add 0 pending
  end;
  let transfer_through steps state =
    List.fold_left (fun state step -> transfer context step state) state steps
  in
  while not (Queue.is_empty pending) do
    let block = Queue.pop pending in
    let after =
      Array.fold_left
        (fun state steps -> transfer_through steps state)
        (Option.get entries.(block))
        actions.steps.(block)
    in
    List.iter
      (fun successor ->
        match entries.(successor) with
        | None ->
            entries.(successor) <- Some after;
            Queue.add successor pending
        | Some known -> (
            match join after ~into:known with
            | Some merged ->
                entries.(successor) <- Some merged;
                Queue.add successor pending
            | None -> ()))
      (Mir.Graph.list_block_successors actions.body block)
  done;
  Array.mapi
    (fun block entry ->
      Option.map
        (fun entry ->
          let state = ref entry in
          Array.map
            (fun steps ->
              Array.of_list
                (List.map
                   (fun step ->
                     let before = !state in
                     state := transfer context step before;
                     before)
                   steps))
            actions.steps.(block))
        entry)
    entries
