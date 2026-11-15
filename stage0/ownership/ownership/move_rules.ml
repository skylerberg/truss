open Context

let copy_fix context title type_ (at : Syntax.span) =
  if copyable context type_ then
    [ Diagnostic.fix title [ Diagnostic.insert (Syntax.Span.zero_width at.stop) ".copy()" ] ]
  else []

type verdict = Moves | Reads | Refused of (context -> Syntax.span -> Types.ty -> unit)

let verdict context (place : Place.t) ~type_ ~is_returned ~is_captured : verdict =
  let shown = show context place in
  let refuse message =
    Refused
      (fun context at type_ ->
        report context Not_owned at ~fixes:(copy_fix context "Pass a copy." type_ at) message)
  in
  let root_kind = if is_captured then Borrowed else kind context place.root in
  if is_returned && root_kind <> Owned then
    if is_view context type_ then Reads
    else
      Refused
        (fun context at type_ ->
          report context Needs_owned at
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
    match (root_kind, place.root) with
    | Borrowed, Constant _ ->
        refuse
          (Printf.sprintf "`%s` is %s, so it cannot be moved. Copy it instead." shown
             (if place.steps = [] then "a constant" else "part of a constant"))
    | Borrowed, _ ->
        refuse
          (Printf.sprintf "`%s` is borrowed, not owned, so it cannot be moved. Copy it instead."
             shown)
    | (Owned | Borrowed_mut), _ -> Moves

let check_body context (body : Mir.Graph.body) moves ~returns_to_caller =
  let place_of (path : Moves.path) : Place.t option =
    match body.locals.(path.local).kind with
    | Source { local; name = Some _; _ } ->
        Some
          {
            root = Local local;
            steps =
              List.map
                (function Moves.Field field | Variant { field; _ } -> Place.Field field)
                path.steps;
          }
    | Source { name = None; _ } | Temporary | Lent _ -> None
  in
  let first_move state (path : Moves.path) =
    match List.sort compare (Moves.moved_at moves state path) with
    | origin :: _ -> Some origin
    | [] -> None
  in
  let reported_use_after_move = Hashtbl.create 8 in
  let check_use_after_move state (place : Mir.place) origin =
    match Moves.path_of_place place with
    | None -> ()
    | Some path -> (
        match Moves.may_be_empty moves state path with
        | Some moved when not (Hashtbl.mem reported_use_after_move moved) -> (
            match (place_of moved, first_move state moved) with
            | Some shown, Some moved_origin ->
                Hashtbl.replace reported_use_after_move moved ();
                let shown = show context shown in
                report context Use_after_move (span context origin)
                  ~notes:[ (span context moved_origin, Printf.sprintf "`%s` is moved here." shown) ]
                  ~fixes:
                    [
                      Diagnostic.fix "Pass a copy at the move instead."
                        (copy_edits context moved_origin);
                    ]
                  (Printf.sprintf "`%s` is used after it was moved." shown)
            | _ -> ())
        | _ -> ())
  in
  let reported_not_reinitialized = Hashtbl.create 8 in
  let check_reinitialized state ~locals ?(moved_in_scope = fun _ -> true) ~at message =
    List.iter
      (fun local ->
        if Moves.lent_mut moves local then
          match Moves.may_be_empty moves state { local; steps = [] } with
          | Some moved when not (Hashtbl.mem reported_not_reinitialized moved) -> (
              match (place_of moved, first_move state moved) with
              | Some shown, Some moved_origin when moved_in_scope moved ->
                  Hashtbl.replace reported_not_reinitialized moved ();
                  let moved_span = span context moved_origin in
                  let root = show context { shown with steps = [] } in
                  report context Not_reinitialized
                    (Option.value ~default:moved_span at)
                    ~notes:(if at = None then [] else [ (moved_span, "It is moved out here.") ])
                    (message (show context shown) root)
              | _ -> ())
          | _ -> ())
      locals
  in
  let all_locals = List.init (Array.length body.locals) Fun.id in
  let scope_end moved root =
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
    else check_reinitialized state ~locals:body.parameters ~at:None scope_end
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
      let state = Moves.entry moves block in
      List.iter
        (fun (statement : Mir.statement) ->
          check_uses state (Moves.statement_uses moves statement);
          List.iter
            (fun (initialized : Moves.path) ->
              match Moves.may_be_empty moves state initialized with
              | Some moved when moved <> initialized && Moves.is_inside ~outer:moved initialized ->
                  check_use_after_move state
                    { root = Local moved.local; projections = [] }
                    statement.origin
              | _ -> ())
            (Moves.given_by statement);
          List.iter
            (fun local -> check_reinitialized state ~locals:[ local ] ~at:None scope_end)
            (Moves.ended_by statement);
          Moves.apply moves state statement)
        basic.statements;
      let at = span context basic.terminator_origin in
      check_uses state (Moves.terminator_uses moves basic);
      match basic.terminator with
      | Return _ -> check_at_return at state
      | Iteration_end { loop } -> (
          match body.blocks.(loop).terminator with
          | For { part; _ } -> check_reinitialized state ~locals:[ part ] ~at:None scope_end
          | _ -> ())
      | Join _ ->
          List.iter
            (fun (blocks, entry) ->
              let branch_entry = Moves.entry moves entry in
              if List.mem block blocks then
                check_reinitialized state ~locals:all_locals
                  ~moved_in_scope:(fun moved -> Moves.may_be_empty moves branch_entry moved = None)
                  ~at:None
                  (fun moved _ ->
                    Printf.sprintf
                      "`%s` is moved out in this branch and not reinitialized in it. If another \
                       branch exits the `concurrent` block early, the code after the block does \
                       not run, so each branch must reinitialize each place it moves out of a \
                       `mut` borrow."
                      moved))
            concurrent_branches
      | _ -> ())
    body.blocks

let analyse context body =
  Moves.analyse ~moving:(fun type_ -> not (plain context type_)) ~tracks:(fun _ -> true) body

let check context (mir : Mir.Graph.t) ~moves ~returns_to_caller =
  check_body context mir.body (moves mir.body) ~returns_to_caller;
  Array.iter
    (fun lambda -> check_body context lambda (moves lambda) ~returns_to_caller:false)
    mir.lambdas
