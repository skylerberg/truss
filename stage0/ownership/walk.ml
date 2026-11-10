(* The walk over a body, in evaluation order: each expression and
   statement, with what it reads, moves, lends, and binds, loops run until
   what may have moved stops changing, and [parallel]. *)

open Syntax
module T = Types
module C = Checked
module Properties = Interface.Properties
open Context
open Flow

type position = Read_position | Owned_position | Mut_position

(* The edits that copy a part that is lent, where one is to be given up. *)
let copy_fix context (value : expression) =
  if copyable context (type_of context value) then
    [ Diagnostic.fix "Copy it." [ Diagnostic.insert value.span.stop ".copy()" ] ]
  else []

let rec expression state (flow : flow) ?(position = Read_position) (value : expression) : flow =
  let context = state.context in
  match value.kind with
  | Mode (mode, inner) when place_of context inner <> None -> (
      let place = Option.get (place_of context inner) in
      let flow = subexpressions state flow inner in
      match mode with
      | Own ->
          Hashtbl.replace context.marks inner.span.start value.span.start;
          if plain context (type_of context inner) then (
            used state flow place inner.span;
            flow)
          else moved_out state flow place inner
      | Mut ->
          used state flow place inner.span;
          changed state place inner.span ~what:"be lent `mut`";
          flow)
  | _ -> (
      match place_of context value with
      | Some place -> (
          let flow = subexpressions state flow value in
          match position with
          | Owned_position when not (plain context (type_of context value)) -> (
              match kind_of context place.root with
              | Owned when place.steps = [] -> moved_out state flow place value
              | _ ->
                  used state flow place value.span;
                  flow)
          | Mut_position ->
              used state flow place value.span;
              changed state place value.span ~what:"be lent `mut`";
              flow
          | _ ->
              used state flow place value.span;
              flow)
      | None -> (
          match value.kind with
          | Mode (Mut, inner) -> expression state flow ~position:Mut_position inner
          | Parenthesized inner -> expression state flow ~position inner
          | _ ->
              (* A part that is lent is never given up: it goes back when
                 the statement is done. *)
              (if position = Owned_position then
                 match lending context value with
                 | Some _ when not (plain context (type_of context value)) ->
                     report context Not_owned value.span ~fixes:(copy_fix context value)
                       "This part is lent, so it cannot be given up: it goes back when the \
                        statement is done. Copy it instead."
                 | _ -> ());
              compound state flow value))

(* Expressions inside a place, such as an index. *)
and subexpressions state flow (value : expression) =
  match value.kind with
  | Member (base, _) | Parenthesized base -> subexpressions state flow base
  | Bracket (base, items) ->
      let flow = subexpressions state flow base in
      List.fold_left
        (fun flow -> function Item item -> expression state flow item | Item_constraint _ -> flow)
        flow items
  | _ -> flow

and compound state flow (value : expression) : flow =
  let context = state.context in
  match value.kind with
  | Call (callee, _) -> call state flow value callee
  | Binary { left; right; _ } -> expression state (expression state flow left) right
  | Return inner ->
      let flow = match inner with Some inner -> returned state flow inner | None -> flow in
      check_restored state flow value.span;
      None
  | Break ->
      (match state.loop_frames with
      | frame :: _ -> frame.breaks <- join frame.breaks flow
      | [] -> ());
      None
  | Continue ->
      (match state.loop_frames with
      | frame :: _ -> frame.continues <- join frame.continues flow
      | [] -> ());
      None
  | Unreachable -> None
  | Try inner ->
      let flow = expression state flow inner in
      check_restored state flow value.span;
      flow
  | With (base, updates) ->
      let flow =
        match base.kind with
        | Mode (Own, _) -> expression state flow base
        | _ -> expression state flow ~position:Owned_position base
      in
      List.fold_left
        (fun flow (update : update) ->
          match update.kind with
          | Update { value = Some value; _ } -> expression state flow ~position:Owned_position value
          | _ -> flow)
        flow updates
  | List items -> List.fold_left (fun flow item -> owned_value state flow item) flow items
  | Map entries ->
      List.fold_left
        (fun flow (key, item) -> owned_value state (owned_value state flow key) item)
        flow entries
  | If { condition; then_; else_ } -> (
      let flow = expression state flow condition in
      let after_then = block state flow then_ in
      match else_ with
      | None -> join after_then flow
      | Some (Else other) -> join after_then (block state flow other)
      | Some (Else_if other) -> join after_then (expression state flow other))
  | Match { scrutinees; arms } ->
      let flow =
        List.fold_left (fun flow scrutinee -> expression state flow scrutinee) flow scrutinees
      in
      List.fold_left
        (fun joined (arm : arm) ->
          let flow =
            match arm.guard with Some guard -> expression state flow guard | None -> flow
          in
          let flow = rebound flow (List.concat_map bound_names arm.patterns) in
          join joined (statement state flow arm.body))
        None arms
  | Lambda { body; _ } ->
      (* A lambda reads what it captures, and its body is a function of its
         own. *)
      (match context.checked.captures.(value.id) with
      | Some captures ->
          List.iter (fun id -> used state flow { root = Local id; steps = [] } value.span) captures
      | None -> ());
      let saved = state.loop_frames in
      state.loop_frames <- [];
      ignore (block state (Some []) body);
      state.loop_frames <- saved;
      flow
  | Provide { implementations; body } ->
      let flow =
        List.fold_left
          (fun flow implementation -> expression state flow implementation)
          flow implementations
      in
      block state flow body
  | Block written -> block state flow written
  | Is { value = tested; pattern; _ } ->
      rebound (expression state flow tested) (bound_names pattern)
  | Prefix (_, inner) | Any inner | Echo inner | Parenthesized inner | Mode (_, inner) ->
      expression state flow inner
  | Range { start; stop; _ } -> (
      let flow = match start with Some start -> expression state flow start | None -> flow in
      match stop with Some stop -> expression state flow stop | None -> flow)
  | Member (base, _) -> expression state flow base
  | Bracket (base, _)
    when Option.is_some context.checked.calls.(value.id) && not (storage (type_of context base)) ->
      call state flow value base
  | Bracket (base, items) ->
      let flow = expression state flow base in
      List.fold_left
        (fun flow -> function Item item -> expression state flow item | Item_constraint _ -> flow)
        flow items
  | String literal ->
      List.fold_left (fun flow (part, _) -> expression state flow part) flow literal.rest
  | Quantified _ -> flow
  | Integer _ | Float _ | True | False | Todo | Self_value | Self_type_value | Name _
  | Expression_error ->
      flow

(* An owned value where one is required: a collection element, or a
   [var]'s initializer. A place there must be marked [own] or copied unless
   it copies implicitly. *)
and owned_value state flow (value : expression) =
  let context = state.context in
  match (value.kind, place_of context value) with
  | Mode (Own, _), _ -> expression state flow value
  | _, None -> expression state flow ~position:Owned_position value
  | _, Some place when not (plain context (type_of context value)) ->
      let shown = show_place context.names place in
      report context Needs_owned value.span
        ~fixes:
          (Diagnostic.fix "Give it up with `own`." [ Diagnostic.insert value.span.start "own " ]
          ::
          (if copyable context (type_of context value) then
             [ Diagnostic.fix "Copy it." [ Diagnostic.insert value.span.stop ".copy()" ] ]
           else []))
        (Printf.sprintf
           "An owned value is needed here, and `%s` is a place. Mark it `own` to give it up, or \
            copy it."
           shown);
      expression state flow value
  | _ -> expression state flow value

(* A returned value moves what it names. A view may be returned only of
   what reached the function through its parameters. *)
and returned state flow (value : expression) =
  let context = state.context in
  (if is_view context (type_of context value) then
     let locals =
       List.filter_map
         (fun place ->
           match place.root with
           | Local id when not (List.mem id context.parameters) -> Some id
           | _ -> None)
         (viewed state value)
     in
     match locals with
     | id :: _ ->
         report context Returns_local_view value.span
           (Printf.sprintf
              "This returns a view of `%s`, which is local to the function, so it would outlive \
               it. A function returns views only of its parameters."
              (Option.value ~default:"a local" (Hashtbl.find_opt context.names id)))
     | [] -> ());
  match place_of context value with
  | Some place when not (plain context (type_of context value)) -> (
      match kind_of context place.root with
      | Owned -> moved_out state flow place value
      | (Viewing | Mut_access) when not (is_view context (type_of context value)) ->
          report context Needs_owned value.span
            ~fixes:
              (if copyable context (type_of context value) then
                 [ Diagnostic.fix "Return a copy." [ Diagnostic.insert value.span.stop ".copy()" ] ]
               else [])
            (Printf.sprintf
               "A returned value must be owned, and `%s` is not owned here. Return a copy."
               (show_place context.names place));
          expression state flow value
      | _ -> expression state flow value)
  | Some _ -> expression state flow value
  | None -> expression state flow ~position:Owned_position value

(* A call: each argument in its parameter's mode, then the loans the call
   makes checked against each other. *)
and call state flow (value : expression) (callee : expression) =
  let context = state.context in
  match context.checked.calls.(value.id) with
  | None -> (
      let flow = expression state flow callee in
      match value.kind with
      | Call (_, arguments) ->
          List.fold_left
            (fun flow (argument : argument) -> expression state flow argument.value)
            flow arguments
      | _ -> flow)
  | Some checked_call ->
      (* A function value is read to be called; anything else's receiver is
         among the arguments. *)
      let flow =
        match checked_call.callee with Function_value -> expression state flow callee | _ -> flow
      in
      let arguments =
        List.filter_map
          (fun (argument : C.argument) ->
            Option.map
              (fun expression -> (argument, expression))
              (find_expression context argument.expression))
          checked_call.arguments
      in
      let flow =
        List.fold_left
          (fun flow ((argument : C.argument), (written : expression)) ->
            let position =
              match argument.mode with
              | Read -> Read_position
              | Mut -> Mut_position
              | Own -> Owned_position
            in
            expression state flow ~position written)
          flow arguments
      in
      (* Two arguments may not overlap when one is lent [mut] or moved: a
         [Plain] place passed [own] is copied, so it lends nothing. *)
      let places =
        List.filter_map
          (fun ((argument : C.argument), (written : expression)) ->
            let inner = match written.kind with Mode (_, inner) -> inner | _ -> written in
            let mode =
              if argument.mode = T.Own && plain context (type_of context inner) then T.Read
              else argument.mode
            in
            Option.map (fun place -> (mode, place, written)) (place_of context inner))
          arguments
      in
      let given = function T.Mut -> "lent `mut`" | _ -> "moved" in
      List.iteri
        (fun index (mode, place, _) ->
          List.iteri
            (fun other (other_mode, other_place, (other_written : expression)) ->
              if other > index && (mode <> T.Read || other_mode <> T.Read) then
                let (exclusive_mode, exclusive), (_, also) =
                  if mode <> T.Read then ((mode, place), (other_mode, other_place))
                  else ((other_mode, other_place), (mode, place))
                in
                match overlap place other_place with
                | Overlap ->
                    report context Conflicting_loan other_written.span
                      (Printf.sprintf "`%s` is %s to this call, so the call cannot use `%s` too."
                         (show_place context.names exclusive)
                         (given exclusive_mode) (show_place context.names also))
                | Maybe_disjoint (first, second) ->
                    context.obligations <- Disjoint { first; second } :: context.obligations
                | No_overlap -> ())
            places)
        places;
      (* A part that is lent to this call lends the whole place it is lent
         from, which an argument before it may not also be when either is
         [mut]. One after it meets the loan as it is evaluated. *)
      let inner_of (written : expression) =
        match written.kind with Mode (_, inner) -> inner | _ -> written
      in
      let placed =
        List.concat
          (List.mapi
             (fun position ((argument : C.argument), written) ->
               match place_of context (inner_of written) with
               | Some place -> [ (position, argument.mode, place) ]
               | None -> [])
             arguments)
      in
      List.iteri
        (fun index ((_ : C.argument), (written : expression)) ->
          let inner = inner_of written in
          match (place_of context inner, lending context inner) with
          | None, Some (lending_call, _) -> (
              match lender context lending_call with
              | Some (lent, lent_mode) ->
                  List.iter
                    (fun (position, mode, place) ->
                      if
                        position < index
                        && (mode <> T.Read || lent_mode <> T.Read)
                        && overlap place lent <> No_overlap
                      then
                        report context Conflicting_loan written.span
                          (Printf.sprintf
                             "This call is given `%s`, and a part that `%s` lends, and one of them \
                              is `mut`. A place is lent whole, for the rest of the statement, when \
                              a part of it is lent."
                             (show_place context.names place) (show_place context.names lent)))
                    placed
              | _ -> ())
          | _ -> ())
        arguments;
      (* A lending call lends the whole place it lends from, for the rest
         of the statement, which is when the method goes on. *)
      (match lending context value with
      | Some (lending_call, _) when lending_call == value -> (
          match lender context value with
          | Some (lent, lent_mode) ->
              state.loans <- { lent; lent_mode; lent_to = To_statement } :: state.loans
          | None -> ())
      | _ -> ());
      flow

(* A statement, at whose end everything a lending call lent in it has gone
   back. *)
and statement state (flow : flow) (written : statement) : flow =
  let before = state.loans in
  let flow = statement_parts state flow written in
  state.loans <- before;
  flow

and statement_parts state (flow : flow) (written : statement) : flow =
  let context = state.context in
  match written.kind with
  | Expression value -> expression state flow value
  | Let { mutable_; pattern; value; else_; _ } ->
      let flow = if mutable_ then owned_value state flow value else expression state flow value in
      (* A name cannot keep a part that is lent, which goes back when the
         statement is done. One of a [Plain] type is copied, unless it is a
         view, which still refers to what lent it. *)
      (if not mutable_ then
         match lending context value with
         | Some _
           when (not (plain context (type_of context value)))
                || is_view context (type_of context value) ->
             report context Keeps_lent_part value.span ~fixes:(copy_fix context value)
               "This part is lent only for this statement, so a name cannot keep it. Use it in \
                this statement, or copy it."
         | _ -> ());
      (* What a binding views, for as long as it is in use. A cursor views
         what its call's read-only arguments view, as a view would. *)
      let holders = bound_names pattern in
      let holds_views =
        is_view context (type_of context value)
        || match type_of context value with T.Cursor _ -> true | _ -> false
      in
      let viewed_places =
        if mutable_ && place_of context value <> None then []
        else if place_of context value <> None && not (plain context (type_of context value)) then
          viewed state value
        else if holds_views then viewed state value
        else []
      in
      if holds_views then
        List.iter
          (fun (temporary : expression) ->
            report context Views_temporary temporary.span
              "This value is dropped at the end of the statement, but what the statement binds \
               still views it. Bind it to a name first, so it lives as long as the view.")
          (viewed_temporaries state value);
      if viewed_places <> [] then
        state.views <- List.map (fun id -> (id, viewed_places)) holders @ state.views;
      (match else_ with Some block_ -> ignore (block state flow block_) | None -> ());
      rebound flow holders
  | Assignment { target; operator; value } -> (
      let flow =
        match operator with
        | Assign -> owned_value state flow value
        | _ -> expression state flow value
      in
      match place_of context target with
      | Some place ->
          let flow = subexpressions state flow target in
          if operator <> Assign then used state flow place target.span;
          assigned state flow place target.span
      | None -> expression state flow target)
  | For { iterable; body; parallel; pattern; _ } ->
      let flow =
        match iterable.kind with
        | Mode (Own, inner) -> (
            match place_of context inner with
            | Some place -> moved_out state flow place inner
            | None -> expression state flow iterable)
        | Mode (Mut, inner) -> (
            match place_of context inner with
            | Some place ->
                used state flow place inner.span;
                changed state place inner.span ~what:"be lent `mut`";
                flow
            | None -> expression state flow iterable)
        | _ -> expression state flow iterable
      in
      let held =
        match iterable.kind with
        | Mode (_, inner) -> place_of context inner
        | _ -> place_of context iterable
      in
      let before = state.parallel_bodies in
      if parallel then state.parallel_bodies <- (body.span.start, bound_names pattern) :: before;
      let flow =
        loop state flow body ~bound:(bound_names pattern) ~held:(Option.to_list held)
          ~held_mode:(match iterable.kind with Mode (Mut, _) -> T.Mut | _ -> T.Read)
          ()
      in
      state.parallel_bodies <- before;
      flow
  | While { condition; body; _ } ->
      let flow = test state flow condition in
      loop state flow body ~held:[] ~held_mode:T.Read ~condition ()
  | Parallel body -> parallel state flow body
  | Proof _ -> flow
  | Assert value | Yield value -> expression state flow value
  | Statement_error -> flow

(* A [while] loop's test, whose lends go back when the test is done, before
   the body runs. *)
and test state flow (condition : expression) =
  let before = state.loans in
  let flow = expression state flow condition in
  state.loans <- before;
  flow

(* A loop's body runs until the moved places stop changing. A loop over a
   place lends it for the whole loop. *)
and loop state flow body ?(bound = []) ~held ~held_mode ?condition () =
  let frame = { breaks = None; continues = None } in
  state.loop_frames <- frame :: state.loop_frames;
  let views_before = state.views in
  (* The collection a loop goes over is lent for the loop: nothing in the
     body may change it, and with [mut], nothing may use it at all. *)
  let loans_before = state.loans in
  state.loans <-
    List.map (fun lent -> { lent; lent_mode = held_mode; lent_to = To_loop }) held @ loans_before;
  let rec iterate entry count =
    frame.continues <- None;
    let after = block state (rebound entry bound) body in
    let after = join after frame.continues in
    let after =
      match condition with Some condition -> test state after condition | None -> after
    in
    let next = join entry after in
    if next = entry || count > 8 then next else iterate next (count + 1)
  in
  let result = iterate flow 0 in
  state.loans <- loans_before;
  state.loop_frames <- List.tl state.loop_frames;
  state.views <- views_before;
  join result frame.breaks

and block state flow (written : block) =
  let views_before = state.views in
  let result =
    List.fold_left (fun flow written -> statement state flow written) flow written.statements
  in
  state.views <- views_before;
  result

(* A function's body: its last expression is what it returns. *)
and function_body state (written : block) =
  let rec go flow = function
    | [] -> flow
    | [ ({ kind = Expression value; _ } : statement) ] -> returned state flow value
    | first :: rest -> go (statement state flow first) rest
  in
  go (Some []) written.statements

(* A [mut] parameter's field moved out must be put back on every path
   before the function returns. *)
and check_restored state (flow : flow) (span : span) =
  match flow with
  | None -> ()
  | Some moved ->
      List.iter
        (fun ((place : place), (moved_span : span)) ->
          match place.root with
          | Local id when List.mem id state.context.mutable_parameters ->
              report state.context Field_not_restored span
                ~notes:[ (moved_span, "It is moved out here.") ]
                (Printf.sprintf
                   "`%s` belongs to the caller, so it must be given a value again before the \
                    function returns."
                   (show_place state.context.names place))
          | _ -> ())
        moved

(* [parallel]: a place one branch changes cannot overlap a place another
   uses. Each branch is walked as ordinary code, gathering what it changes
   and reads. *)
and parallel state flow (body : block) =
  let context = state.context in
  let outer = state.effects in
  let flow, branches =
    List.fold_left
      (fun (flow, branches) (branch : statement) ->
        let effects = { changes = []; reads = [] } in
        state.effects <- Some effects;
        let flow = statement state flow branch in
        (flow, branches @ [ effects ]))
      (flow, []) body.statements
  in
  state.effects <- outer;
  (* What the branches do, the block does, for a [parallel] around it. *)
  Option.iter
    (fun outer ->
      List.iter
        (fun effects ->
          outer.changes <- effects.changes @ outer.changes;
          outer.reads <- effects.reads @ outer.reads)
        branches)
    outer;
  List.iteri
    (fun index effects ->
      List.iteri
        (fun other others ->
          if other <> index then
            List.iter
              (fun (place, span) ->
                let used = others.reads @ List.map fst others.changes in
                if List.exists (fun other_place -> overlap other_place place = Overlap) used then
                  report context Parallel_conflict span
                    (Printf.sprintf
                       "One branch of this `parallel` block changes `%s`, which another branch \
                        uses."
                       (show_place context.names place)))
              effects.changes)
        branches)
    branches;
  (* Two indexes of one collection, one changed by a branch and one used by
     another, are disjoint only if the prover shows it: each pair of
     branches once, each change of either against all the other uses. *)
  List.iteri
    (fun index effects ->
      List.iteri
        (fun other others ->
          if other > index then
            let pairs mine theirs =
              List.concat_map
                (fun (changed, _) -> List.map (fun used -> (changed, used)) theirs)
                mine
            in
            List.iter
              (fun (changed, used) ->
                match overlap changed used with
                | Maybe_disjoint (first, second) ->
                    context.obligations <- Disjoint { first; second } :: context.obligations
                | Overlap | No_overlap -> ())
              (pairs effects.changes (others.reads @ List.map fst others.changes)
              @ pairs others.changes effects.reads))
        branches)
    branches;
  flow
