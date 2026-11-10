(* The flow of the walk: the places that may have been moved, the views and
   loans live at a point, and what each read, change, and move of a place
   must respect. *)

open Syntax
module T = Types
module C = Checked
open Context

(* The places that may have been moved, each with where. [None] is a point
   no path reaches, after [return], [break], or [continue]. *)
type flow = (place * span) list option

let join (left : flow) (right : flow) : flow =
  match (left, right) with
  | None, other | other, None -> other
  | Some left, Some right -> Some (left @ List.filter (fun entry -> not (List.mem entry left)) right)

(* The views live at a point: what holds views, a local or what the caller
   keeps, with the places it views. One holder may have several entries. *)
type views = (root * place list) list
type loop_frame = { mutable breaks : flow; mutable continues : flow }

(* A place lent for a stretch of code: by a loop over it, for the loop, or by
   a lending call, for the rest of its statement. Read-only, so the code may
   not change it, or [mut], so the code may not use it at all. *)
type lender = To_loop | To_statement
type loan = { lent : place; lent_mode : T.mode; lent_to : lender }

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

let lent_mut_message context (loan : loan) =
  let place = show_place context.names loan.lent in
  match loan.lent_to with
  | To_loop -> Printf.sprintf "`%s` is lent `mut` to the loop, so its body cannot use it." place
  | To_statement ->
      Printf.sprintf
        "`%s` is lent `mut` for the rest of this statement, so the statement cannot use it again."
        place

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
        report state.context Conflicting_loan span (lent_mut_message state.context loan))
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
          report context Conflicting_loan span (lent_mut_message context loan)
        else
          report context Changed_while_viewed span
            (Printf.sprintf
               (match loan.lent_to with
               | To_loop -> format_of_string "`%s` cannot %s while the loop goes over it."
               | To_statement ->
                   "`%s` cannot %s while a part of it is lent, which lasts this statement.")
               (show_place context.names place) what))
    state.loans;
  (* Each iteration of a [parallel for] runs at once with the others, so it
     may change only what is its own: its element and its locals. *)
  List.iter
    (fun (start, own) ->
      let outside =
        match place.root with
        | Self_root | Constant_root _ -> true
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
      (* A local is in use while it is read again, and what the caller
         keeps is in use for good. *)
      let in_use =
        match holder with
        | Local id when not (kept_by_caller context { root = holder; steps = [] }) ->
            live context id ~at:span.start
        | Local _ | Self_root | Constant_root _ -> true
      in
      if List.exists (fun lent_place -> overlap lent_place place <> No_overlap) lent && in_use then
        report context Changed_while_viewed span
          (Printf.sprintf "`%s` cannot %s while `%s`, which views it, is still in use."
             (show_place context.names place) what (show_root context.names holder)))
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
    match (kind_of context place.root, place.root) with
    | Viewing, Constant_root _ ->
        report context Not_owned value.span ~fixes:copy_fix
          (Printf.sprintf "`%s` is %s, so it cannot be moved. Copy it instead." shown
             (if place.steps = [] then "a constant" else "part of a constant"));
        flow
    | Viewing, _ ->
        report context Not_owned value.span ~fixes:copy_fix
          (Printf.sprintf "`%s` is a view, not owned here, so it cannot be moved. Copy it instead."
             shown);
        flow
    | Mut_access, _ when place.steps = [] ->
        report context Not_owned value.span ~fixes:copy_fix
          (Printf.sprintf
             "`%s` is lent `mut`, so it cannot be moved away; a field of it can, if it is put back."
             shown);
        flow
    | (Owned | Mut_access), _ ->
        changed state place value.span ~what:"be moved";
        context.moves <- value.id :: context.moves;
        Option.map (fun moved -> (place, value.span) :: moved) flow

(* Names a pattern binds afresh, so whatever was moved out of them before,
   as on an earlier time round a loop, is theirs again. *)
let rebound (flow : flow) ids =
  Option.map
    (List.filter (fun ((moved : place), _) ->
         match moved.root with
         | Local id -> not (List.mem id ids)
         | Self_root | Constant_root _ -> true))
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

(* What a holder is known to view, or [None] when nothing was noted of
   it. *)
let held state (holder : root) =
  match List.filter (fun (other, _) -> other = holder) state.views with
  | [] -> None
  | entries -> Some (List.concat_map snd entries)

(* The places a value may view.

   A place named as a value is a view of that place, and of what the place
   holds views of. But a local that is itself a view, or that only views
   another place, has nothing of its own to view: a value read from it views
   what the local was noted to view, and the local itself only when nothing
   was noted. So [let part = items[0..2]] and then [part] views [items].

   A call's result views what its arguments let it: those lent to it, which
   are the read-only and [mut] ones that are not [Plain], and those that
   are views. A slice views what its collection does, and a lambda the
   locals it captures. *)
let rec viewed state (value : expression) : place list =
  let context = state.context in
  match value.kind with
  | Parenthesized inner | Echo inner | Mode (_, inner) -> viewed state inner
  | Bracket (base, [ Item { kind = Range _; _ } ]) when place_of context base = None ->
      viewed state base
  | Lambda _ -> (
      match context.checked.captures.(value.id) with
      | Some captures -> List.map (fun id -> { root = Local id; steps = [] }) captures
      | None -> [])
  | _ -> (
      match place_of context value with
      | Some place -> (
          let known = held state place.root in
          let its_own =
            match place.root with
            | Self_root | Constant_root _ -> true
            | Local id ->
                List.mem id context.parameters
                || kind_of context place.root = Owned
                   && not
                        (match context.checked.local_types.(id) with
                        | Some type_ -> is_view context type_
                        | None -> false)
          in
          match known with
          | Some places when not its_own -> places
          | _ -> Option.value ~default:[] known @ [ place ])
      | None -> (
          match context.checked.calls.(value.id) with
          | Some call -> List.concat_map (viewed state) (lent_arguments context call)
          | None -> []))

(* The arguments of a call that what the call makes, or what it is given
   [mut], may come to view. *)
and lent_arguments context (call : C.call) =
  List.filter_map
    (fun (argument : C.argument) ->
      match find_expression context argument.expression with
      | Some expression
        when (argument.mode <> T.Own && not (plain context (type_of context expression)))
             || is_view context (type_of context expression) ->
          Some expression
      | _ -> None)
    call.arguments

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

(* A place comes to hold views: of what is assigned to it, or of what a call
   that takes it [mut] was given, which the call may have kept in it. Its
   holder views them from then on. What the caller keeps must not view what
   ends with the function. *)
let stored state (place : place) (span : span) (places : place list) =
  let context = state.context in
  if places <> [] && not (List.mem (place.root, places) state.views) then
    state.views <- (place.root, places) :: state.views;
  if kept_by_caller context place then
    match List.find_opt (ends_with_function context) places with
    | Some local ->
        report context Stores_local_view span
          (Printf.sprintf
             "This puts a view of `%s` in `%s`, which the caller keeps, so the view would outlive \
              `%s`. What the caller keeps views only what reached the function through its \
              parameters."
             (show_root context.names local.root)
             (show_root context.names place.root)
             (show_root context.names local.root))
    | None -> ()
