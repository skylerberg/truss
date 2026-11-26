let merge_known_on_paths (paths : (Logic.term * State.frame) list) =
  let merge_known pick ~is_same ~on_differing =
    let keys =
      List.fold_left
        (fun keys ((_, frame) : Logic.term * State.frame) ->
          Locals.fold (fun key _ keys -> Locals.add key () keys) (pick frame) keys)
        Locals.empty paths
    in
    Locals.mapi
      (fun key () ->
        let each =
          List.map (fun (condition, frame) -> (condition, Locals.find_opt key (pick frame))) paths
        in
        match each with
        | (_, Some one) :: rest
          when List.for_all
                 (fun (_, other) ->
                   match other with Some other -> is_same one other | None -> false)
                 rest ->
            one
        | _ -> on_differing each)
      keys
  in
  let guard condition = List.map (fun (on, known) -> (Logic.( &&& ) condition on, known)) in
  let guard_each each =
    List.concat_map
      (fun (condition, known) -> guard condition (Option.value ~default:[] known))
      each
  in
  let aliases = merge_known (fun frame -> frame.aliases) ~is_same:( = ) ~on_differing:guard_each in
  let lends = merge_known (fun frame -> frame.lends) ~is_same:( == ) ~on_differing:guard_each in
  (aliases, lends)

let name_path_condition (frame : State.frame) condition =
  match condition with
  | Logic.Boolean _ | Logic.Symbol _ -> condition
  | _ when (not frame.makes_obligations) || Logic.mentions frame.bound condition -> condition
  | _ ->
      let path = Facts.declare_fresh frame "path" Logic.Bool in
      Facts.define frame path condition;
      path

let merge ?value_type ~condition (paths : (Logic.term * State.frame * Logic.term option) list) =
  let first =
    match paths with (_, first, _) :: _ -> first | [] -> Facts.raise_bug "no paths meet"
  in
  let is_expression = not first.makes_obligations in
  let aliases, lends = merge_known_on_paths (List.map (fun (on, frame, _) -> (on, frame)) paths) in
  let merged = { first with condition; aliases; lends } in
  let choose values =
    match List.rev values with
    | (_, _, last) :: earlier ->
        List.fold_left (fun otherwise (on, _, term) -> Logic.ite on term otherwise) last earlier
    | [] -> Facts.raise_bug "a value that no path gives"
  in
  let define prefix sort (values : (Logic.term * State.frame * Logic.term) list) =
    (match values with
    | (_, _, term) :: rest when List.exists (fun (_, _, other) -> other <> term) rest ->
        List.iter (fun (_, frame, merged) -> Callbacks.check_read frame merged) values
    | _ -> ());
    match values with
    | (_, _, term) :: rest
      when List.for_all (fun (_, _, other) -> other == term || other = term) rest ->
        term
    | _
      when List.for_all
             (fun (_, _, term) -> match term with Logic.Boolean _ -> true | _ -> false)
             values ->
        Logic.disjunction
          (List.filter_map
             (fun (on, _, term) -> if term = Logic.Boolean true then Some on else None)
             values)
    | _
      when is_expression
           || List.exists
                (fun (on, (frame : State.frame), term) ->
                  Logic.mentions first.bound on
                  || Logic.mentions first.bound frame.condition
                  || Logic.mentions first.bound term)
                values ->
        choose values
    | _ ->
        let symbol = Facts.declare_fresh first prefix sort in
        List.iter
          (fun (_, (frame : State.frame), term) ->
            Facts.add_axiom first (Logic.( ==> ) frame.condition (Logic.equal symbol term)))
          values;
        symbol
  in
  let find_held pick =
    let values =
      List.filter_map
        (fun (on, frame, _) -> Option.map (fun term -> (on, frame, term)) (pick frame))
        paths
    in
    if List.length values = List.length paths then Some values else None
  in
  let keys =
    List.fold_left
      (fun keys (_, (frame : State.frame), _) ->
        Locals.fold (fun key _ keys -> Locals.add key () keys) frame.locals keys)
      Locals.empty paths
  in
  let locals =
    Locals.mapi
      (fun id () ->
        match find_held (fun frame -> Locals.find_opt id frame.locals) with
        | Some values ->
            let sort =
              match Encoding.find_local_type first id with
              | Some ty -> Encoding.sort_of ty
              | None -> (
                  match values with (_, _, Logic.Boolean _) :: _ -> Logic.Bool | _ -> Logic.Int)
            in
            define "joined" sort values
        | None -> (
            match
              List.find_map
                (fun (_, (frame : State.frame), _) -> Locals.find_opt id frame.locals)
                paths
            with
            | Some term -> term
            | None -> Facts.raise_bug "a local that no path binds"))
      keys
  in
  let types =
    List.fold_left
      (fun types (_, (frame : State.frame), _) ->
        Locals.union (fun _ ty _ -> Some ty) types frame.types)
      Locals.empty paths
  in
  let self =
    match (first.self_type, find_held (fun frame -> frame.self)) with
    | Some ty, Some values -> Some (define "self" (Encoding.sort_of ty) values)
    | _ -> first.self
  in
  let list_renamings (frame : State.frame) =
    let renamings =
      Locals.fold
        (fun id joined renamings ->
          match Locals.find_opt id frame.locals with
          | Some incoming when incoming != joined && incoming <> joined ->
              (incoming, joined) :: renamings
          | _ -> renamings)
        locals []
    in
    match (frame.self, self) with
    | Some incoming, Some joined when incoming <> joined -> (incoming, joined) :: renamings
    | _ -> renamings
  in
  let spent =
    Costs.join_spent first.spent
      ~paths:
        (List.map
           (fun (on, (frame : State.frame), _) -> (on, list_renamings frame, frame.spent))
           paths)
      ~name:(fun amount ->
        if Logic.mentions first.bound amount then amount
        else
          let symbol = Facts.declare_fresh first "spent" Logic.Int in
          Facts.define first symbol amount;
          symbol)
  in
  let value =
    let values =
      List.filter_map
        (fun (on, frame, value) -> Option.map (fun term -> (on, frame, term)) value)
        paths
    in
    if values = [] || List.length values <> List.length paths then None
    else
      match value_type with
      | Some ty -> Some (define "value" (Encoding.sort_of ty) values)
      | None -> Some (choose values)
  in
  let merge_part pick =
    match (Option.map Encoding.sort_of first.lent_part_type, find_held pick) with
    | Some sort, Some values -> Some (define "part" sort values)
    | _ -> pick first
  in
  ( {
      merged with
      locals;
      types;
      spent;
      self;
      result = merge_part (fun frame -> frame.result);
      final_result = merge_part (fun frame -> frame.final_result);
    },
    value )

let join ?value_type frames =
  match frames with
  | [] -> None
  | [ (frame, value) ] -> Some (frame, value)
  | (first, _) :: _ ->
      let condition =
        name_path_condition first
          (Logic.disjunction (List.map (fun ((frame : State.frame), _) -> frame.condition) frames))
      in
      Some
        (merge ?value_type ~condition
           (List.map (fun ((frame : State.frame), value) -> (frame.condition, frame, value)) frames))

let join_frames frames = Option.map fst (join (List.map (fun frame -> (frame, None)) frames))
