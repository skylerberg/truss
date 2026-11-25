module Place_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Moves.path
end))

type verdict = Moves | Reads | Refused of (Context.context -> Core.origin -> Types.ty -> unit)

let decide_move context (place : Place.t) ~origin ~type_ ~is_returned ~is_captured : verdict =
  let shown = Context.find_place context place in
  let refuse make =
    Refused
      (fun context at type_ ->
        Context.report context (make at (Context.find_copy context type_ origin)))
  in
  let root_mode : Language.Mode.t =
    if is_captured then Read else Context.classify_binding_mode context place.root
  in
  let views_literal = (not is_captured) && Context.views_literal context place.root in
  if Context.find_place_without_keyword context origin = Some Mut then
    refuse (fun at copy -> Needs_lent_mut { at; place = shown; copy })
  else if is_returned && root_mode <> Own then
    if Context.is_view context type_ then Reads
    else
      refuse (fun at copy ->
          match Context.find_owned_scrutinee context place.root with
          | Some scrutinee -> Returned_view_of_scrutinee { at; place = shown; scrutinee; copy }
          | None -> Returned_unowned { at; place = shown; views_literal; copy })
  else if List.exists (function Place.Element _ | Range _ -> true | Field _ -> false) place.steps
  then
    match List.rev place.steps with
    | Range _ :: _ ->
        Refused
          (fun context at type_ ->
            Context.report context
              (Moved_range
                 {
                   at;
                   place = shown;
                   copy = Context.find_copy context type_ origin;
                   view_type = Types.make_view type_;
                 }))
    | Element _ :: _ | Field _ :: _ | [] ->
        refuse (fun at copy -> Moved_element { at; place = shown; copy })
  else
    match (root_mode, place.root) with
    | Read, Constant _ -> refuse (fun at copy -> Moved_constant { at; place = shown; copy })
    | Read, _ when views_literal ->
        refuse (fun at copy -> Moved_literal_view { at; place = shown; copy })
    | Read, _ ->
        refuse (fun at copy ->
            match Context.find_owned_scrutinee context place.root with
            | Some scrutinee -> Moved_view_of_scrutinee { at; place = shown; scrutinee; copy }
            | None -> Moved_view { at; place = shown; copy })
    | (Own | Mut), _ when Context.find_place_without_keyword context origin = Some Own ->
        refuse (fun at copy -> Needs_own_keyword { at; place = shown; copy })
    | (Own | Mut), _ -> Moves

let check_body context (body : Mir.Graph.body) moves ~returns_to_caller =
  let find_place (path : Moves.path) : Place.t option =
    match body.locals.(path.local).kind with
    | Source { local; is_binding = true; _ } ->
        Some
          {
            root = Local local;
            steps =
              List.map
                (function
                  | Mir.Field field | Variant_field { field; _ } -> Place.Field field
                  | Element _ | Range _ ->
                      Compiler_bug.raise_bug ~stage:"Ownership"
                        "a moved path through an element or a range")
                path.projections;
          }
    | Source { is_binding = false; _ } | Temporary | Lent _ -> None
  in
  let find_first_move state (path : Moves.path) =
    match List.sort compare (Moves.list_moved_at moves state path) with
    | origin :: _ -> Some origin
    | [] -> None
  in
  let moved_types = Hashtbl.create 8 in
  let record_moved_type (use : Moves.use) =
    match use.operand with
    | Some (Use { type_; _ } | Borrow { type_; _ } | Take { type_; _ } | Immediate { type_; _ })
      when use.moves ->
        Hashtbl.replace moved_types use.origin type_
    | Some _ | None -> ()
  in
  Array.iter
    (fun (basic : Mir.Graph.basic_block) ->
      List.iter
        (fun statement -> List.iter record_moved_type (Moves.list_statement_uses moves statement))
        basic.statements;
      List.iter record_moved_type (Moves.list_terminator_uses moves basic))
    body.blocks;
  let read_moved_type origin =
    match Hashtbl.find_opt moved_types origin with
    | Some type_ -> type_
    | None -> Compiler_bug.raise_bug ~stage:"Ownership" "a move has no moving use"
  in
  let reported_use_after_move = Place_table.create 8 in
  let check_use_after_move state (place : Mir.place) origin =
    match Moves.find_place_path place with
    | None -> ()
    | Some path -> (
        match Moves.find_possibly_empty moves state path with
        | Some moved when not (Place_table.mem reported_use_after_move moved) -> (
            match (find_place moved, find_first_move state moved) with
            | Some shown, Some moved_origin ->
                Place_table.replace reported_use_after_move moved ();
                Context.report context
                  (Use_after_move
                     {
                       at = origin;
                       place = Context.find_place context shown;
                       moved = moved_origin;
                       copy = Context.find_copy context (read_moved_type moved_origin) moved_origin;
                     })
            | _ -> ())
        | _ -> ())
  in
  let reported_not_reinitialized = Place_table.create 8 in
  let check_reinitialized state ~locals ?(is_moved_in_scope = fun _ -> true) make_diagnostic =
    List.iter
      (fun local ->
        if Moves.is_lent_mut moves local then
          match Moves.find_possibly_empty moves state { local; projections = [] } with
          | Some moved when not (Place_table.mem reported_not_reinitialized moved) -> (
              match (find_place moved, find_first_move state moved) with
              | Some shown, Some moved_origin when is_moved_in_scope moved ->
                  Place_table.replace reported_not_reinitialized moved ();
                  Context.report context
                    (make_diagnostic ~moved:moved_origin (Context.find_place context shown))
              | _ -> ())
          | _ -> ())
      locals
  in
  let all_locals = List.init (Array.length body.locals) Fun.id in
  let at_scope_end ~moved place : Catalog.Ownership.t =
    Not_reinitialized_at_scope_end { moved; place }
  in
  let check_at_return at state =
    if returns_to_caller then
      check_reinitialized state ~locals:all_locals (fun ~moved place ->
          Not_reinitialized_at_return { at; moved; place })
    else check_reinitialized state ~locals:body.parameters at_scope_end
  in
  let concurrent_branches =
    Array.to_list body.blocks
    |> List.concat_map (fun (basic : Mir.Graph.basic_block) ->
        match basic.terminator with
        | Fork { concurrent = true; branches; _ } ->
            List.map (fun (branch : Mir.Graph.branch) -> (branch.blocks, branch.entry)) branches
        | _ -> [])
  in
  let check_uses state uses =
    let statement_state = Moves.copy state in
    List.iter
      (fun (use : Moves.use) ->
        check_use_after_move statement_state use.place use.origin;
        if use.moves then Moves.move_out moves statement_state use.place ~origin:use.origin)
      uses
  in
  Array.iteri
    (fun block (basic : Mir.Graph.basic_block) ->
      let state = Moves.copy_entry_state moves block in
      List.iter
        (fun (statement : Mir.Graph.statement) ->
          check_uses state (Moves.list_statement_uses moves statement);
          List.iter
            (fun (initialized : Moves.path) ->
              match Moves.find_possibly_empty moves state initialized with
              | Some moved when moved <> initialized && Moves.is_inside ~outer:moved initialized ->
                  check_use_after_move state
                    { root = Local moved.local; projections = [] }
                    statement.origin
              | _ -> ())
            (Moves.list_given_by statement);
          List.iter
            (fun local -> check_reinitialized state ~locals:[ local ] at_scope_end)
            (Moves.list_ended statement);
          Moves.apply moves state statement)
        basic.statements;
      check_uses state (Moves.list_terminator_uses moves basic);
      match basic.terminator with
      | Return _ -> check_at_return basic.terminator_origin state
      | Iteration_end { loop } ->
          check_reinitialized state
            ~locals:[ (Mir.Graph.read_loop_head body loop).part ]
            at_scope_end
      | Join _ ->
          List.iter
            (fun (blocks, entry) ->
              let branch_entry = Moves.copy_entry_state moves entry in
              if List.mem block blocks then
                check_reinitialized state ~locals:all_locals
                  ~is_moved_in_scope:(fun moved ->
                    Moves.find_possibly_empty moves branch_entry moved = None)
                  (fun ~moved place -> Not_reinitialized_in_branch { moved; place }))
            concurrent_branches
      | Goto _ | Branch _ | For _ | Fork _ | Yield _ | Cancel _ | Resume _ | Unreachable
      | Written_unreachable | Todo ->
          ())
    body.blocks

let analyse context body =
  Moves.analyse
    ~is_moving:(fun type_ -> not (Context.is_plain context type_))
    ~tracks:(fun _ -> true)
    body

let check context (mir : Mir.Graph.t) ~read_moves ~returns_to_caller =
  check_body context mir.body (read_moves mir.body) ~returns_to_caller;
  Array.iter
    (fun lambda -> check_body context lambda (read_moves lambda) ~returns_to_caller:false)
    mir.lambdas
