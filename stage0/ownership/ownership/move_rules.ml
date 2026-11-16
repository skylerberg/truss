module Place_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Moves.path
end))

let copy_fix context title type_ (at : Source.Definition_span.t) =
  if Context.is_copyable context type_ then
    [
      Diagnostic.fix title
        [ Diagnostic.insert (Source.Definition_span.make_zero_width at.stop) ".copy()" ];
    ]
  else []

type verdict =
  | Moves
  | Reads
  | Refused of (Context.context -> Source.Definition_span.t -> Types.ty -> unit)

let decide_move context (place : Place.t) ~origin ~type_ ~is_returned ~is_captured : verdict =
  let shown = Context.show context place in
  let refuse message =
    Refused
      (fun context at type_ ->
        Context.report context Not_owned at ~fixes:(copy_fix context "Copy it." type_ at) message)
  in
  let root_mode : Types.mode =
    if is_captured then Read else Context.classify_binding_mode context place.root
  in
  if is_returned && root_mode <> Own then
    if Context.is_view context type_ then Reads
    else
      Refused
        (fun context at type_ ->
          Context.report context Needs_owned at
            ~fixes:(copy_fix context "Return a copy." type_ at)
            (Printf.sprintf
               "A returned value must be owned, and `%s` is not owned here. Return a copy." shown))
  else if List.exists (function Place.Element _ -> true | Field _ -> false) place.steps then
    refuse
      (Printf.sprintf
         "`%s` is an element, which cannot be moved out of its collection. Copy it, or take it out \
          with a method such as `remove`."
         shown)
  else
    match (root_mode, place.root) with
    | Read, Constant _ ->
        refuse
          (Printf.sprintf "`%s` is %s, so it cannot be moved. Copy it instead." shown
             (if place.steps = [] then "a constant" else "part of a constant"))
    | Read, _ ->
        refuse
          (Printf.sprintf "`%s` is borrowed, not owned, so it cannot be moved. Copy it instead."
             shown)
    | (Own | Mut), _ when Hashtbl.mem context.places_without_own origin ->
        Refused
          (fun context at type_ ->
            Context.report context Needs_owned at
              ~fixes:
                (Diagnostic.fix "Move it with `own`."
                   [ Diagnostic.insert (Source.Definition_span.make_zero_width at.start) "own " ]
                :: copy_fix context "Copy it." type_ at)
              (Printf.sprintf
                 "An owned value is needed here, and `%s` is a place. Pass it `own` to move it, or \
                  copy it."
                 shown))
    | (Own | Mut), _ -> Moves

let check_body context (body : Mir.Graph.body) moves ~returns_to_caller =
  let find_place (path : Moves.path) : Place.t option =
    match body.locals.(path.local).kind with
    | Source { local; name = Some _; _ } ->
        Some
          {
            root = Local local;
            steps =
              List.map
                (function Mir.Field field | Variant_field { field; _ } -> Place.Field field)
                path.projections;
          }
    | Source { name = None; _ } | Temporary | Lent _ -> None
  in
  let find_first_move state (path : Moves.path) =
    match List.sort compare (Moves.list_moved_at moves state path) with
    | origin :: _ -> Some origin
    | [] -> None
  in
  let reported_use_after_move = Place_table.create 8 in
  let check_use_after_move state (place : Mir.place) origin =
    match Moves.path_of_place place with
    | None -> ()
    | Some path -> (
        match Moves.find_possibly_empty moves state path with
        | Some moved when not (Place_table.mem reported_use_after_move moved) -> (
            match (find_place moved, find_first_move state moved) with
            | Some shown, Some moved_origin ->
                Place_table.replace reported_use_after_move moved ();
                let shown = Context.show context shown in
                Context.report context Use_after_move
                  (Context.locate_origin context origin)
                  ~notes:
                    [
                      ( Context.locate_origin context moved_origin,
                        Printf.sprintf "`%s` is moved here." shown );
                    ]
                  ~fixes:
                    [
                      Diagnostic.fix "Pass a copy at the move instead."
                        (Context.copy_edits context moved_origin);
                    ]
                  (Printf.sprintf "`%s` is used after it was moved." shown)
            | _ -> ())
        | _ -> ())
  in
  let reported_not_reinitialized = Place_table.create 8 in
  let check_reinitialized state ~locals ?(is_moved_in_scope = fun _ -> true) ~at make_message =
    List.iter
      (fun local ->
        if Moves.is_lent_mut moves local then
          match Moves.find_possibly_empty moves state { local; projections = [] } with
          | Some moved when not (Place_table.mem reported_not_reinitialized moved) -> (
              match (find_place moved, find_first_move state moved) with
              | Some shown, Some moved_origin when is_moved_in_scope moved ->
                  Place_table.replace reported_not_reinitialized moved ();
                  let moved_span = Context.locate_origin context moved_origin in
                  let root = Context.show context { shown with steps = [] } in
                  Context.report context Not_reinitialized
                    (Option.value ~default:moved_span at)
                    ~notes:(if at = None then [] else [ (moved_span, "It is moved out here.") ])
                    (make_message (Context.show context shown) root)
              | _ -> ())
          | _ -> ())
      locals
  in
  let all_locals = List.init (Array.length body.locals) Fun.id in
  let describe_scope_end moved root =
    Printf.sprintf
      "`%s` is moved out here and not reinitialized. `%s` is borrowed `mut`, so every part of it \
       must be initialized when its loop iteration, its `match` arm, or its lambda ends."
      moved root
  in
  let check_at_return at state =
    if returns_to_caller then
      check_reinitialized state ~locals:all_locals ~at:(Some at) (fun moved _ ->
          Printf.sprintf
            "`%s` is moved out and not reinitialized. The caller owns it, so assign it a value \
             before the function returns."
            moved)
    else check_reinitialized state ~locals:body.parameters ~at:None describe_scope_end
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
            (fun local -> check_reinitialized state ~locals:[ local ] ~at:None describe_scope_end)
            (Moves.list_ended statement);
          Moves.apply moves state statement)
        basic.statements;
      let at = Context.locate_origin context basic.terminator_origin in
      check_uses state (Moves.list_terminator_uses moves basic);
      match basic.terminator with
      | Return _ -> check_at_return at state
      | Iteration_end { loop } ->
          check_reinitialized state
            ~locals:[ (Mir.Graph.read_loop_head body loop).part ]
            ~at:None describe_scope_end
      | Join _ ->
          List.iter
            (fun (blocks, entry) ->
              let branch_entry = Moves.copy_entry_state moves entry in
              if List.mem block blocks then
                check_reinitialized state ~locals:all_locals
                  ~is_moved_in_scope:(fun moved ->
                    Moves.find_possibly_empty moves branch_entry moved = None)
                  ~at:None
                  (fun moved _ ->
                    Printf.sprintf
                      "`%s` is moved out in this branch and not reinitialized in it. If another \
                       branch exits the `concurrent` block early, the code after the block does \
                       not run, so each branch must reinitialize each place it moves out of a \
                       `mut` borrow."
                      moved))
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
