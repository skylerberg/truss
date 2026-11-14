(* Moves, checked on the control-flow graph of a core form. The check
   prevents use after move.

   A forward dataflow analysis computes, for each point, the places that may
   have been moved on some path to it. A use of a place that overlaps a
   moved place is an error. Whether a place can be moved at all needs no
   dataflow: it depends on the place and on how its root is bound. *)
open Context

(* The effect of a [Move] point, decided from the place and from how its
   root is bound. *)
type verdict =
  | Moves  (** The place is moved. *)
  | Reads  (** A view is returned: the place is only read. *)
  | Refused of (context -> Syntax.span -> Types.ty -> unit)  (** The move is an error. *)

let verdict context (place : Place.t) ~type_ ~returned ~captured : verdict =
  let copy title type_ (at : Syntax.span) =
    if copyable context type_ then
      [ Diagnostic.fix title [ Diagnostic.insert (Syntax.Span.zero_width at.stop) ".copy()" ] ]
    else []
  in
  let shown = show context place in
  let refuse message =
    Refused
      (fun context at type_ ->
        report context Not_owned at ~fixes:(copy "Pass a copy." type_ at) message)
  in
  let root_kind = if captured then Borrowed else kind context place.root in
  if returned && root_kind <> Owned then
    if is_view context type_ then Reads
    else
      Refused
        (fun context at type_ ->
          report context Needs_owned at ~fixes:(copy "Return a copy." type_ at)
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

(* The moves the graph refuses: a move of a place its root does not own,
   and of a part that a lending call lends. Whether a place can be moved
   needs no dataflow: it depends on the place and on how its root is
   bound. *)
let check_refused context (graph : Graph.t) =
  Array.iter
    (fun (point : Graph.point) ->
      let at = span context point.origin in
      match point.action with
      | Move { place; type_; returned; captured } -> (
          match verdict context place ~type_ ~returned ~captured with
          | Refused refuse -> refuse context at type_
          | Moves | Reads -> ())
      | Move_out_of_lent type_ ->
          report context Not_owned at
            ~fixes:
              (if copyable context type_ then
                 [
                   Diagnostic.fix "Copy it."
                     [ Diagnostic.insert (Syntax.Span.zero_width at.stop) ".copy()" ];
                 ]
               else [])
            "This part is lent, so it cannot be moved: the loan ends when the statement ends. Copy \
             it instead."
      | _ -> ())
    graph.points

(* Where code is: a statement of a block, or its terminator. *)
type position = { block : Mir.block; index : int }

(* The checks of moves on one body's MIR, with the move analysis code
   generation drops by. A place whose type is not plain moves where it is
   read by value. The checks prevent a use after move, and a place of the
   caller's that a [mut] borrow ends with nothing in it. [returns] says
   whether the body's end returns to a caller that owns its [mut]
   parameters' places: a function's does, and a lambda's ends a scope of
   its own. *)
let check_body context (body : Mir.body) ~returns =
  let moves =
    Moves.analyse ~moving:(fun type_ -> not (plain context type_)) ~tracks:(fun _ -> true) body
  in
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
  let predecessors = Array.make (Array.length body.blocks) [] in
  let loops = Mir.iteration_loops body in
  Array.iteri
    (fun block (basic : Mir.basic_block) ->
      let successors =
        match basic.terminator with
        | Iteration_end -> Option.to_list (Hashtbl.find_opt loops block)
        | terminator -> Mir.successors terminator
      in
      List.iter
        (fun successor -> predecessors.(successor) <- block :: predecessors.(successor))
        successors)
    body.blocks;
  (* Where a path that may hold nothing at a position was moved out of, and
     the block of the move: the nearest move of a place that overlaps it on
     some path back, which no assignment of the whole path comes between. *)
  let moved_at (path : Moves.path) { block; index } =
    let visited = Hashtbl.create 16 in
    let found = ref None in
    let moving (uses : Moves.use list) =
      List.find_map
        (fun (use : Moves.use) ->
          match Moves.path_of_place use.place with
          | Some moved when use.moves && Moves.overlaps moved path -> Some use.origin
          | _ -> None)
        (List.rev uses)
    in
    let rec back block before =
      if !found = None && not (Hashtbl.mem visited (block, before)) then begin
        Hashtbl.replace visited (block, before) ();
        let basic = body.blocks.(block) in
        let statements = Array.of_list basic.statements in
        let rec scan index =
          if index < 0 then
            List.iter (fun predecessor -> back predecessor None) predecessors.(block)
          else
            let statement = statements.(index) in
            match moving (Moves.statement_uses moves statement) with
            | Some origin -> found := Some (origin, block)
            | None ->
                if
                  not
                    (List.exists
                       (fun given -> Moves.is_inside ~outer:given path)
                       (Moves.given_by statement)
                    || List.mem path.local (Moves.ended_by statement))
                then scan (index - 1)
        in
        match before with
        | Some index -> scan (index - 1)
        | None -> (
            match
              moving
                (Moves.terminator_uses_of moves basic.terminator ~origin:basic.terminator_origin)
            with
            | Some origin -> found := Some (origin, block)
            | None -> scan (Array.length statements - 1))
      end
    in
    back block (Some index);
    !found
  in
  let used_after_move = Hashtbl.create 8 in
  (* A use of a place that overlaps a place that may have been moved out:
     a use after move. Each moved place is reported once. *)
  let check_use state position (place : Mir.place) origin =
    match Moves.path_of_place place with
    | None -> ()
    | Some path -> (
        match Moves.may_be_empty moves state path with
        | Some moved when not (Hashtbl.mem used_after_move moved) -> (
            match (place_of moved, moved_at moved position) with
            | Some shown, Some (moved_origin, _) ->
                Hashtbl.replace used_after_move moved ();
                let shown = show context shown in
                report context Use_after_move (span context origin)
                  ~notes:[ (span context moved_origin, Printf.sprintf "`%s` is moved here." shown) ]
                  ~fixes:
                    [
                      Diagnostic.fix "Pass a copy at the move instead."
                        (copy_at context moved_origin);
                    ]
                  (Printf.sprintf "`%s` is used after it was moved." shown)
            | _ -> ())
        | _ -> ())
  in
  let not_reinitialized = Hashtbl.create 8 in
  (* A [mut] borrow must end with the place fully initialized, because its
     owner uses the place afterwards, so a place moved out of one must be
     given a value again before the borrow ends: [locals] are the borrows
     that end here. [within] says whether a move counts, by its block. *)
  let check_given state position ~locals ?(within = fun _ -> true) ~at message =
    List.iter
      (fun local ->
        if Moves.lent_mut moves local then
          match Moves.may_be_empty moves state { local; steps = [] } with
          | Some moved when not (Hashtbl.mem not_reinitialized moved) -> (
              match (place_of moved, moved_at moved position) with
              | Some shown, Some (moved_origin, moved_block) when within moved_block ->
                  Hashtbl.replace not_reinitialized moved ();
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
  let returned at state position =
    if returns then
      check_given state position ~locals:all_locals ~at:(Some at) (fun moved _ ->
          Printf.sprintf
            "`%s` is moved out and not reinitialized. The caller owns it, so assign it a value \
             before the function returns."
            moved)
    else check_given state position ~locals:body.parameters ~at:None scope_end
  in
  (* The branches of [concurrent] blocks, by the blocks each holds. *)
  let branches =
    Array.to_list body.blocks
    |> List.concat_map (fun (basic : Mir.basic_block) ->
        match basic.terminator with
        | Fork { concurrent = true; branches; _ } ->
            List.map (fun (branch : Mir.branch) -> branch.blocks) branches
        | _ -> [])
  in
  Array.iteri
    (fun block (basic : Mir.basic_block) ->
      let state = Moves.entry moves block in
      List.iteri
        (fun index (statement : Mir.statement) ->
          let position = { block; index } in
          let working = Moves.copy state in
          List.iter
            (fun (use : Moves.use) ->
              check_use working position use.place use.origin;
              if use.moves then Moves.move_out moves working use.place)
            (Moves.statement_uses moves statement);
          (* Giving a part of a moved place a value uses the moved place. *)
          List.iter
            (fun (given : Moves.path) ->
              match Moves.may_be_empty moves state given with
              | Some moved when moved <> given && Moves.is_inside ~outer:moved given ->
                  check_use state position
                    { root = Local moved.local; projections = [] }
                    statement.origin
              | _ -> ())
            (Moves.given_by statement);
          List.iter
            (fun local -> check_given state position ~locals:[ local ] ~at:None scope_end)
            (Moves.ended_by statement);
          Moves.apply moves state statement)
        basic.statements;
      let position = { block; index = List.length basic.statements } in
      let at = span context basic.terminator_origin in
      let working = Moves.copy state in
      List.iter
        (fun (use : Moves.use) ->
          check_use working position use.place use.origin;
          if use.moves then Moves.move_out moves working use.place)
        (Moves.terminator_uses_of moves basic.terminator ~origin:basic.terminator_origin);
      match basic.terminator with
      | Return _ | Exit_tasks { exit = Exit_return _; _ } -> returned at state position
      | Yield _ when context.yields ->
          check_given state position ~locals:all_locals ~at:(Some at) (fun moved _ ->
              Printf.sprintf
                "`%s` is moved out and not reinitialized before this `yield`. The caller's loop \
                 may `break` here, and then the method never resumes."
                moved)
      | Iteration_end -> (
          match Hashtbl.find_opt loops block with
          | Some loop -> (
              match body.blocks.(loop).terminator with
              | For { part; _ } -> check_given state position ~locals:[ part ] ~at:None scope_end
              | _ -> ())
          | None -> ())
      | Join _ ->
          List.iter
            (fun blocks ->
              if List.mem block blocks then
                check_given state position ~locals:all_locals
                  ~within:(fun moved -> List.mem moved blocks)
                  ~at:None
                  (fun moved _ ->
                    Printf.sprintf
                      "`%s` is moved out in this branch and not reinitialized in it. If another \
                       branch exits the `concurrent` block early, the code after the block does \
                       not run, so each branch must reinitialize each place it moves out of a \
                       `mut` borrow."
                      moved))
            branches
      | _ -> ())
    body.blocks

let check context (mir : Mir.t) ~returns =
  check_body context mir.body ~returns;
  Array.iter (check_body context ~returns:false) mir.lambdas
