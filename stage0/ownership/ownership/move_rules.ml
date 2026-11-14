(* The rules of moves. Whether a place can be moved at all needs no
   dataflow: it depends on the place and on how its root is bound. The move
   analysis code generation drops by says which places may hold nothing at
   each point of a body's MIR, and a use of one is a use after move. *)
open Context

(* The fix that copies a value at [at], where its type has a copy. *)
let copy_fix context title type_ (at : Syntax.span) =
  if copyable context type_ then
    [ Diagnostic.fix title [ Diagnostic.insert (Syntax.Span.zero_width at.stop) ".copy()" ] ]
  else []

(* The effect of a [Move] action, decided from the place and from how its
   root is bound. *)
type verdict =
  | Moves  (** The place is moved. *)
  | Reads  (** A view is returned: the place is only read. *)
  | Refused of (context -> Syntax.span -> Types.ty -> unit)  (** The move is an error. *)

let verdict context (place : Place.t) ~type_ ~returned ~captured : verdict =
  let shown = show context place in
  let refuse message =
    Refused
      (fun context at type_ ->
        report context Not_owned at ~fixes:(copy_fix context "Pass a copy." type_ at) message)
  in
  let root_kind = if captured then Borrowed else kind context place.root in
  if returned && root_kind <> Owned then
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

(* The checks of moves on one body's MIR, with the move analysis code
   generation drops by. A place whose type is not plain moves where it is
   read by value. The checks prevent a use after move, and a place of the
   caller's that a [mut] borrow ends with nothing in it. [returns] says
   whether the body's end returns to a caller that owns its [mut]
   parameters' places: a function's does, and a lambda's ends a scope of
   its own. *)
let check_body context (body : Mir.body) moves ~returns =
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
  (* The first move that may have left a path that holds nothing empty, or
     [None] where none did: the path was not yet given a value. *)
  let moved_at state (path : Moves.path) =
    match List.sort compare (Moves.moved_at moves state path) with
    | origin :: _ -> Some origin
    | [] -> None
  in
  let used_after_move = Hashtbl.create 8 in
  (* A use of a place that overlaps a place that may have been moved out:
     a use after move. Each moved place is reported once. *)
  let check_use state (place : Mir.place) origin =
    match Moves.path_of_place place with
    | None -> ()
    | Some path -> (
        match Moves.may_be_empty moves state path with
        | Some moved when not (Hashtbl.mem used_after_move moved) -> (
            match (place_of moved, moved_at state moved) with
            | Some shown, Some moved_origin ->
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
     reinitialized before the borrow ends: [locals] are the borrows
     that end here. [within] says whether a path's move counts. *)
  let check_given state ~locals ?(within = fun _ -> true) ~at message =
    List.iter
      (fun local ->
        if Moves.lent_mut moves local then
          match Moves.may_be_empty moves state { local; steps = [] } with
          | Some moved when not (Hashtbl.mem not_reinitialized moved) -> (
              match (place_of moved, moved_at state moved) with
              | Some shown, Some moved_origin when within moved ->
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
  let returned at state =
    if returns then
      check_given state ~locals:all_locals ~at:(Some at) (fun moved _ ->
          Printf.sprintf
            "`%s` is moved out and not reinitialized. The caller owns it, so assign it a value \
             before the function returns."
            moved)
    else check_given state ~locals:body.parameters ~at:None scope_end
  in
  (* The branches of [concurrent] blocks: the blocks each holds, and where
     it starts. *)
  let branches =
    Array.to_list body.blocks
    |> List.concat_map (fun (basic : Mir.basic_block) ->
        match basic.terminator with
        | Fork { concurrent = true; branches; _ } ->
            List.map (fun (branch : Mir.branch) -> (branch.blocks, branch.entry)) branches
        | _ -> [])
  in
  (* Checks reads in evaluation order: a read after a move in the same
     statement, as in [f(own x, x)], is a use after move. *)
  let check_uses state uses =
    let working = Moves.copy state in
    List.iter
      (fun (use : Moves.use) ->
        check_use working use.place use.origin;
        if use.moves then Moves.move_out moves working use.place ~origin:use.origin)
      uses
  in
  Array.iteri
    (fun block (basic : Mir.basic_block) ->
      let state = Moves.entry moves block in
      List.iter
        (fun (statement : Mir.statement) ->
          check_uses state (Moves.statement_uses moves statement);
          (* Giving a part of a moved place a value uses the moved place. *)
          List.iter
            (fun (given : Moves.path) ->
              match Moves.may_be_empty moves state given with
              | Some moved when moved <> given && Moves.is_inside ~outer:moved given ->
                  check_use state { root = Local moved.local; projections = [] } statement.origin
              | _ -> ())
            (Moves.given_by statement);
          List.iter
            (fun local -> check_given state ~locals:[ local ] ~at:None scope_end)
            (Moves.ended_by statement);
          Moves.apply moves state statement)
        basic.statements;
      let at = span context basic.terminator_origin in
      check_uses state (Moves.terminator_uses moves basic);
      match basic.terminator with
      | Return _ -> returned at state
      | Iteration_end { loop } -> (
          match body.blocks.(loop).terminator with
          | For { part; _ } -> check_given state ~locals:[ part ] ~at:None scope_end
          | _ -> ())
      | Join _ ->
          List.iter
            (fun (blocks, entry) ->
              (* A place the branch moved held a value where it started. *)
              let started = Moves.entry moves entry in
              if List.mem block blocks then
                check_given state ~locals:all_locals
                  ~within:(fun moved -> Moves.may_be_empty moves started moved = None)
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

(* The move analysis of a body, by the ownership checker's rule: a value
   whose type is not plain moves where it is read by value. *)
let analyse context body =
  Moves.analyse ~moving:(fun type_ -> not (plain context type_)) ~tracks:(fun _ -> true) body

let check context (mir : Mir.t) ~moves ~returns =
  check_body context mir.body (moves mir.body) ~returns;
  Array.iter (fun lambda -> check_body context lambda (moves lambda) ~returns:false) mir.lambdas
