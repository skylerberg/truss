(* The flow of the walk: the places that may have been moved, the views and
   loans live at a point, and what each read, change, and move of a place
   must respect. *)

open Syntax
module T = Types
module C = Checked
module Properties = Interface.Properties
open Context

(* The places that may have been moved, each with where. [None] is a point
   no path reaches, after [return], [break], or [continue]. *)
type flow = (place * span) list option

let join (left : flow) (right : flow) : flow =
  match (left, right) with
  | None, other | other, None -> other
  | Some left, Some right -> Some (left @ List.filter (fun entry -> not (List.mem entry left)) right)

(* The views live at a point: each local that holds loans, with the places
   it holds them on. *)
type views = (id * place list) list
type loop_frame = { mutable breaks : flow; mutable continues : flow }

(* A place lent for a stretch of code, by a loop over it: read-only, so the
   code may not change it, or [mut], so the code may not use it at all. *)
type loan = { lent : place; lent_mode : T.mode }

(* What a stretch of code changes and reads, gathered for [parallel]. *)
type effects = { mutable changes : (place * span) list; mutable reads : place list }

type state = {
  context : context;
  mutable views : views;
  mutable loop_frames : loop_frame list;
  mutable loans : loan list;
  mutable parallel_bodies : (int * id list) list;
      (** The [parallel for] bodies the code is in: where each starts, and the locals its pattern
          binds, which each iteration has its own of. *)
  mutable effects : effects option;
}

let new_state context =
  { context; views = []; loop_frames = []; loans = []; parallel_bodies = []; effects = None }

let lent_mut_message context place =
  Printf.sprintf "`%s` is lent `mut` to the loop, so its body cannot use it."
    (show_place context.names place)

(* The edits that copy where a place was moved: [.copy()] after it, and
   its [own] mark removed. *)
let copy_at context (moved : span) =
  match Hashtbl.find_opt context.marks moved.start with
  | Some mark_start ->
      [
        Diagnostic.delete (Source.span mark_start moved.start);
        Diagnostic.insert moved.stop ".copy()";
      ]
  | None -> [ Diagnostic.insert moved.stop ".copy()" ]

let used state (flow : flow) (place : place) (span : span) =
  Option.iter (fun effects -> effects.reads <- place :: effects.reads) state.effects;
  List.iter
    (fun loan ->
      if loan.lent_mode = T.Mut && overlap loan.lent place <> No_overlap then
        report state.context Conflicting_loan span (lent_mut_message state.context loan.lent))
    state.loans;
  match flow with
  | None -> ()
  | Some moved -> (
      match
        List.find_opt
          (fun (moved_place, _) -> is_prefix moved_place place || is_prefix place moved_place)
          moved
      with
      | Some (moved_place, moved_span) ->
          let key = (moved_place.root, moved_place.steps) in
          if not (List.mem key state.context.reported) then begin
            state.context.reported <- key :: state.context.reported;
            let shown = show_place state.context.names moved_place in
            report state.context Use_after_move span
              ~notes:[ (moved_span, Printf.sprintf "`%s` is moved here." shown) ]
              ~fixes:
                [
                  Diagnostic.fix "Pass a copy at the move instead."
                    (copy_at state.context moved_span);
                ]
              (Printf.sprintf "`%s` is used after it was moved." shown)
          end
      | None -> ())

(* A change to a place while a view of an overlapping place is live. *)
let changed state (place : place) (span : span) ~what =
  let context = state.context in
  Option.iter (fun effects -> effects.changes <- (place, span) :: effects.changes) state.effects;
  List.iter
    (fun loan ->
      if overlap loan.lent place <> No_overlap then
        if loan.lent_mode = T.Mut then
          report context Conflicting_loan span (lent_mut_message context loan.lent)
        else
          report context Changed_while_viewed span
            (Printf.sprintf "`%s` cannot %s while the loop goes over it."
               (show_place context.names place) what))
    state.loans;
  (* Each iteration of a [parallel for] runs at once with the others, so it
     may change only what is its own: its element and its locals. *)
  List.iter
    (fun (start, own) ->
      let outside =
        match place.root with
        | Self_root -> true
        | Local id ->
            (not (List.mem id own))
            && Option.value ~default:0 (Hashtbl.find_opt context.declared id) < start
      in
      if outside then
        report context Parallel_conflict span
          "A `parallel for` may change only its own element and its own locals.")
    state.parallel_bodies;
  List.iter
    (fun (holder, lent) ->
      if
        List.exists (fun lent_place -> overlap lent_place place <> No_overlap) lent
        && live state.context holder ~at:span.start
      then
        report state.context Changed_while_viewed span
          (Printf.sprintf "`%s` cannot %s while `%s`, which views it, is still in use."
             (show_place state.context.names place)
             what
             (Option.value ~default:"a view" (Hashtbl.find_opt state.context.names holder))))
    state.views

let moved_out state (flow : flow) (place : place) (value : expression) =
  let context = state.context in
  used state flow place value.span;
  (* Only an owned place can be moved, and never an element, which a method
     such as [remove] takes out instead. *)
  let shown = show_place context.names place in
  let copy_fix =
    if copyable context (type_of context value) then
      [ Diagnostic.fix "Pass a copy." [ Diagnostic.insert value.span.stop ".copy()" ] ]
    else []
  in
  if List.exists (function Element _ -> true | Field _ -> false) place.steps then begin
    report context Not_owned value.span ~fixes:copy_fix
      (Printf.sprintf
         "`%s` is an element, which cannot be moved out of its collection. Copy it, or take it out \
          with a method such as `remove`."
         shown);
    flow
  end
  else
    match kind_of context place.root with
    | Viewing ->
        report context Not_owned value.span ~fixes:copy_fix
          (Printf.sprintf "`%s` is a view, not owned here, so it cannot be moved. Copy it instead."
             shown);
        flow
    | Mut_access when place.steps = [] ->
        report context Not_owned value.span ~fixes:copy_fix
          (Printf.sprintf
             "`%s` is lent `mut`, so it cannot be moved away; a field of it can, if it is put back."
             shown);
        flow
    | Owned | Mut_access ->
        changed state place value.span ~what:"be moved";
        context.moves <- value.id :: context.moves;
        Option.map (fun moved -> (place, value.span) :: moved) flow

(* Names a pattern binds afresh, so whatever was moved out of them before,
   as on an earlier time round a loop, is theirs again. *)
let rebound (flow : flow) ids =
  Option.map
    (List.filter (fun ((moved : place), _) ->
         match moved.root with Local id -> not (List.mem id ids) | Self_root -> true))
    flow

let assigned state (flow : flow) (place : place) (span : span) =
  (match flow with
  | Some moved -> (
      match
        List.find_opt
          (fun (moved_place, _) -> is_prefix moved_place place && moved_place <> place)
          moved
      with
      | Some (moved_place, _) -> used state flow moved_place span
      | None -> ())
  | None -> ());
  changed state place span ~what:"change";
  Option.map (List.filter (fun (moved_place, _) -> not (is_prefix place moved_place))) flow

(* The places a value of a view type may view: those of the read-only and
   view-typed arguments of the call that made it, of a slice's collection,
   and of the locals a lambda captures. *)
let rec viewed state (value : expression) : place list =
  let context = state.context in
  match value.kind with
  | Parenthesized inner | Echo inner -> viewed state inner
  | Bracket (base, [ Item { kind = Range _; _ } ]) -> (
      match place_of context base with Some place -> [ place ] | None -> viewed state base)
  | Lambda _ -> (
      match context.checked.captures.(value.id) with
      | Some captures -> List.map (fun id -> { root = Local id; steps = [] }) captures
      | None -> [])
  | _ -> (
      match place_of context value with
      | Some place -> (
          match place.root with
          | Local id ->
              (match List.assoc_opt id state.views with Some held -> held | None -> [])
              @ [ place ]
          | Self_root -> [ place ])
      | None -> (
          match context.checked.calls.(value.id) with
          | Some call ->
              List.concat_map
                (fun (argument : C.argument) ->
                  match find_expression context argument.expression with
                  | Some expression
                    when (argument.mode = T.Read && not (plain context (type_of context expression)))
                         || is_view context (type_of context expression) ->
                      viewed state expression
                  | _ -> [])
                call.arguments
          | None -> []))

(* The temporaries a value of a view type views: owned values that only
   the statement holds, passed read-only to the call that made it. A string
   literal without interpolation is in static memory, so it lives forever. *)
and viewed_temporaries state (value : expression) : expression list =
  let context = state.context in
  match value.kind with
  | Parenthesized inner | Echo inner -> viewed_temporaries state inner
  | Bracket (base, [ Item { kind = Range _; _ } ]) -> owned_temporary state base
  | _ when place_of context value <> None -> []
  | _ -> (
      match context.checked.calls.(value.id) with
      | Some call ->
          List.concat_map
            (fun (argument : C.argument) ->
              match find_expression context argument.expression with
              | Some expression when argument.mode = T.Read -> owned_temporary state expression
              | Some expression when is_view context (type_of context expression) ->
                  viewed_temporaries state expression
              | _ -> [])
            call.arguments
      | None -> [])

and owned_temporary state (value : expression) =
  let context = state.context in
  let type_ = type_of context value in
  match value.kind with
  | Parenthesized inner -> owned_temporary state inner
  | String { rest = []; tag = None; _ } -> []
  | Lambda _ -> []
  | _ when place_of context value <> None -> []
  | _ when plain context type_ -> []
  | _ when is_view context type_ -> viewed_temporaries state value
  | _ -> [ value ]

and find_expression context id = Hashtbl.find_opt context.nodes id
