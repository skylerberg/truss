(* Moves, checked on the control-flow graph of a core form.

   A forward analysis finds, for each point, the places that may have been
   moved on some path to it. A use of a place that overlaps a moved place
   is an error. The rules on what may be moved need no flow: they depend
   on the place and on how its root is bound. *)

module T = Types
open Graph
open Context

(* What a [Move] point does, by the place and the kind of its root. *)
type verdict =
  | Moves  (** The place is moved. *)
  | Reads  (** A view is returned: the place is only read. *)
  | Refused of (context -> Syntax.span -> T.ty -> unit)  (** The move is an error. *)

let verdict context (place : Place.t) ~type_ ~returned ~captured : verdict =
  let copy title type_ (at : Syntax.span) =
    if copyable context type_ then [ Diagnostic.fix title [ Diagnostic.insert at.stop ".copy()" ] ]
    else []
  in
  let shown = show context place in
  let refuse message =
    Refused
      (fun context at type_ ->
        report context Not_owned at ~fixes:(copy "Pass a copy." type_ at) message)
  in
  let root_kind = if captured then Viewing else kind context place.root in
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
    | Viewing, Constant _ ->
        refuse
          (Printf.sprintf "`%s` is %s, so it cannot be moved. Copy it instead." shown
             (if place.steps = [] then "a constant" else "part of a constant"))
    | Viewing, _ ->
        refuse
          (Printf.sprintf "`%s` is a view, not owned here, so it cannot be moved. Copy it instead."
             shown)
    | (Owned | Mut_access), _ -> Moves

(* A moved place, with the point that moved it. *)
type moved = Place.t * int

let transfer verdicts (index : int) (point : point) (before : moved list) : moved list =
  match point.action with
  | Move { place; _ } when verdicts.(index) = Some Moves ->
      if List.mem (place, index) before then before else (place, index) :: before
  | Assign place -> List.filter (fun (moved, _) -> not (Place.is_prefix place moved)) before
  | Bind locals | Ends locals ->
      List.filter
        (fun ((moved : Place.t), _) ->
          match moved.root with
          | Local local -> not (List.mem local locals)
          | Constant _ | Environment -> true)
        before
  | Enter | Read _ | Move _ | Take_lent _ | Mutate _ | Exit | Task_end _ | Suspend _ | Hold _
  | Store _ | Return_view _ | Views_temporary _ | Keeps_lent_part _ | Gives_function _
  | Write_through _ | Arguments _ ->
      before

(* The places that may have been moved before each point. *)
let moved_before (graph : Graph.t) verdicts : moved list array =
  let count = Array.length graph.points in
  let before = Array.make count [] in
  let pending = Queue.create () in
  let queued = Array.make count false in
  let reached = Array.make count false in
  let push index =
    if not queued.(index) then begin
      queued.(index) <- true;
      Queue.add index pending
    end
  in
  List.iter push graph.entries;
  while not (Queue.is_empty pending) do
    let index = Queue.pop pending in
    queued.(index) <- false;
    let after = transfer verdicts index graph.points.(index) before.(index) in
    List.iter
      (fun successor ->
        let known = before.(successor) in
        let added = List.filter (fun entry -> not (List.mem entry known)) after in
        if added <> [] || not reached.(successor) then begin
          reached.(successor) <- true;
          before.(successor) <- known @ added;
          push successor
        end)
      graph.points.(index).successors
  done;
  before

let check context (graph : Graph.t) =
  let points = graph.points in
  let verdicts =
    Array.map
      (fun (point : point) ->
        match point.action with
        | Move { place; type_; returned; captured; _ } ->
            Some (verdict context place ~type_ ~returned ~captured)
        | _ -> None)
      points
  in
  let before = moved_before graph verdicts in
  let reported = Hashtbl.create 8 in
  (* A use of a place that overlaps a moved place. One report for each
     moved place. *)
  let used index (place : Place.t) =
    match
      List.find_opt
        (fun ((moved : Place.t), _) -> Place.is_prefix moved place || Place.is_prefix place moved)
        (List.sort (fun (_, first) (_, second) -> compare first second) before.(index))
    with
    | Some (moved, moved_at) when not (Hashtbl.mem reported moved) ->
        Hashtbl.replace reported moved ();
        let moved_span = span context points.(moved_at).origin in
        let shown = show context moved in
        report context Use_after_move
          (span context points.(index).origin)
          ~notes:[ (moved_span, Printf.sprintf "`%s` is moved here." shown) ]
          ~fixes:[ Diagnostic.fix "Pass a copy at the move instead." (copy_at context moved_span) ]
          (Printf.sprintf "`%s` is used after it was moved." shown)
    | _ -> ()
  in
  (* A place that is lent [mut] goes back to its owner, so what is moved
     out of it must be given a value again before it goes back. [roots]
     says which of the moved places go back at the point. *)
  let reported = Hashtbl.create 8 in
  let reinitialized ?(moved_within = fun _ -> true) index ~roots ~at message =
    List.iter
      (fun ((moved : Place.t), moved_at) ->
        if
          kind context moved.root = Mut_access
          && roots moved.root && moved_within moved_at
          && not (Hashtbl.mem reported moved)
        then begin
          Hashtbl.replace reported moved ();
          let moved_span = span context points.(moved_at).origin in
          report context Not_reinitialized
            (Option.value ~default:moved_span at)
            ~notes:(if at = None then [] else [ (moved_span, "It is moved out here.") ])
            (message (show context moved) (show_root context moved.root))
        end)
      before.(index)
  in
  let bound locals : Place.root -> bool = function
    | Local local -> List.mem local locals
    | Constant _ | Environment -> false
  in
  Array.iteri
    (fun index (point : point) ->
      let at = span context point.origin in
      match point.action with
      | Read place | Mutate place -> used index place
      | Move { place; use; type_; _ } -> (
          used index place;
          match verdicts.(index) with
          | Some Moves -> context.moves <- use :: context.moves
          | Some (Refused refuse) -> refuse context at type_
          | Some Reads | None -> ())
      | Take_lent type_ ->
          report context Not_owned at
            ~fixes:
              (if copyable context type_ then
                 [ Diagnostic.fix "Copy it." [ Diagnostic.insert at.stop ".copy()" ] ]
               else [])
            "This part is lent, so it cannot be given up: it goes back when the statement is done. \
             Copy it instead."
      | Assign place -> (
          (* Assigning a part of a moved place uses the moved place. *)
          match
            List.find_opt
              (fun (moved, _) -> Place.is_prefix moved place && moved <> place)
              before.(index)
          with
          | Some (moved, _) -> used index moved
          | None -> ())
      | Exit ->
          reinitialized index
            ~roots:(fun _ -> true)
            ~at:(Some at)
            (fun moved _ ->
              Printf.sprintf
                "`%s` belongs to the caller, so it must be given a value again before the function \
                 returns."
                moved)
      | Task_end { first; limit } ->
          reinitialized index
            ~moved_within:(fun point -> first <= point && point < limit)
            ~roots:(fun _ -> true)
            ~at:None
            (fun moved _ ->
              Printf.sprintf
                "`%s` is moved out in this branch and is not given a value again in it. If another \
                 branch leaves early, the code after the `concurrent` block does not run, so a \
                 branch puts back what it takes out of a place that is lent `mut`."
                moved)
      | Suspend _ ->
          if context.yields then
            reinitialized index
              ~roots:(fun _ -> true)
              ~at:(Some at)
              (fun moved _ ->
                Printf.sprintf
                  "`%s` must be given a value again before this `yield`, because a loop may stop \
                   the method here."
                  moved)
      | Bind locals | Ends locals ->
          reinitialized index ~roots:(bound locals) ~at:None (fun moved root ->
              Printf.sprintf
                "`%s` is moved out here and is not given a value again. `%s` is lent `mut`, so \
                 every part of it must have a value when its loop iteration, its `match` arm, or \
                 its lambda ends."
                moved root)
      | Enter | Hold _ | Store _ | Return_view _ | Views_temporary _ | Keeps_lent_part _
      | Gives_function _ | Write_through _ | Arguments _ ->
          ())
    points
