(* Moves, loans, and views, within each function. See TYPECHECKER.md,
   "Ownership: moves, loans, and views".

   Truss has only structured control flow, so the analysis follows the
   tree in evaluation order: the places that may have been moved flow
   forward, joined by union where branches meet, and loops run until
   nothing changes. A loan is live while the value that holds it may still
   be used: a later use reaches a point unless the two are in different
   arms of one branch, and a loop's back edge reaches the uses before a
   point in its body. *)

open Syntax
module T = Types
module C = Checked
module Properties = Interface.Properties

(* Places *)

type root = Local of id | Self_root

(* An index whose value the checker cannot compare stands for some element. *)
type step = Field of string | Element of id
type place = { root : root; steps : step list }

let show_root names = function
  | Local id -> Option.value ~default:"this" (Hashtbl.find_opt names id)
  | Self_root -> "self"

let show_place names place =
  show_root names place.root
  ^ String.concat ""
      (List.map (function Field name -> "." ^ name | Element _ -> "[...]") place.steps)

type overlap = No_overlap | Overlap | Maybe_disjoint of id * id

(* Two places overlap when one is a prefix of the other. Two different
   indexes of one collection may not, which the prover decides. *)
let overlap left right =
  if left.root <> right.root then No_overlap
  else
    let rec go left right =
      match (left, right) with
      | [], _ | _, [] -> Overlap
      | Field a :: left, Field b :: right -> if a = b then go left right else No_overlap
      | Element a :: left, Element b :: right -> (
          if a = b then go left right
          else match go left right with No_overlap -> No_overlap | _ -> Maybe_disjoint (a, b))
      | _ :: left, _ :: right -> go left right
    in
    go left.steps right.steps

let is_prefix prefix place =
  prefix.root = place.root
  &&
  let rec go = function
    | [], _ -> true
    | Field a :: prefix, Field b :: place -> a = b && go (prefix, place)
    | Element _ :: prefix, Element _ :: place -> go (prefix, place)
    | _ -> false
  in
  go (prefix.steps, place.steps)

(* Locals *)

(* What a local holds: an owned value, a view of a place, or [mut] access
   to one, which lasts only for its call, iteration, or block. *)
type kind = Owned | Viewing | Mut_access

type context = {
  database : Query.database;
  definition : definition;
  resolved : Resolve.resolved;
  checked : C.t;
  bounds : T.parameter -> T.trait_reference list;
  kinds : (id, kind) Hashtbl.t;
  names : (id, string) Hashtbl.t;
  nodes : (id, expression) Hashtbl.t;  (** Every expression of the definition, by its id. *)
  mutable parameters : id list;  (** The body's parameters, which a returned view may come from. *)
  mutable mutable_parameters : id list;
  mutable self_kind : kind option;
  paths : (int, (id * int) list) Hashtbl.t;
      (** For each position, the branches it is in: a branch's id and the arm. *)
  loops : (int, id list) Hashtbl.t;  (** For each position, the loops it is in. *)
  uses : (id, int list) Hashtbl.t;  (** For each local, where it is read. *)
  declared : (id, int) Hashtbl.t;  (** Where each local is bound. *)
  mutable diagnostics : Diagnostic.t list;
  mutable reported : (root * step list) list;
  mutable moves : id list;
  mutable obligations : C.obligation list;
  marks : (int, int) Hashtbl.t;
      (** Where the [own] mark of a moved place starts, by the place's start. *)
}

let report context ?(fixes = []) ?(notes = []) code (span : span) message =
  context.diagnostics <-
    Diagnostic.make ~fixes
      ~notes:
        (List.map (fun ((span : span), text) -> (Source.span span.start span.stop, text)) notes)
      ~code:(Ownership code)
      (Source.span span.start span.stop)
      message
    :: context.diagnostics

let type_of context (value : expression) =
  Option.value ~default:T.Error context.checked.types.(value.id)

let plain context type_ = Properties.plain context.database ~bounds:context.bounds type_
let copyable context type_ = Properties.copyable context.database ~bounds:context.bounds type_
let is_view context type_ = Properties.is_view context.database ~bounds:context.bounds type_

let rec place_of context (value : expression) : place option =
  match value.kind with
  | Name path -> (
      match context.resolved.names.(path.last.id) with
      | Some (Local id) -> Some { root = Local id; steps = [] }
      | _ -> None)
  | Self_value -> Some { root = Self_root; steps = [] }
  | Member (base, member) -> (
      match context.checked.meanings.(value.id) with
      | Some (Field_read _) ->
          Option.map
            (fun place -> { place with steps = place.steps @ [ Field member.text ] })
            (place_of context base)
      | _ -> None)
  | Bracket (base, [ Item key ])
    when context.resolved.brackets.(value.id) = Some Index
         ||
         match context.checked.calls.(value.id) with
         | Some { callee = Trait_method { name = "at"; _ }; _ } -> true
         | _ -> false -> (
      match key.kind with
      | Range _ -> None
      | _ ->
          Option.map
            (fun place -> { place with steps = place.steps @ [ Element key.id ] })
            (place_of context base))
  | Parenthesized inner -> place_of context inner
  | _ -> None

let kind_of context = function
  | Local id -> Option.value ~default:Owned (Hashtbl.find_opt context.kinds id)
  | Self_root -> Option.value ~default:Viewing context.self_kind

(* Reachability, for liveness *)

(* Whether the code at [later] can run after the code at [earlier]: it comes
   after it, outside every branch arm the earlier is in that it is not in
   itself; or a loop around both brings it round again. *)
let reachable context ~earlier ~later ~declared =
  let path position = Option.value ~default:[] (Hashtbl.find_opt context.paths position) in
  let loops position = Option.value ~default:[] (Hashtbl.find_opt context.loops position) in
  let exclusive =
    List.exists
      (fun (branch, arm) ->
        match List.assoc_opt branch (path later) with Some other -> other <> arm | None -> false)
      (path earlier)
  in
  (later > earlier && not exclusive)
  || List.exists
       (fun loop ->
         List.mem loop (loops later)
         && not
              (List.mem loop
                 (match Hashtbl.find_opt context.loops declared with
                 | Some loops -> loops
                 | None -> [])))
       (loops earlier)

let live context holder ~at =
  let declared = Option.value ~default:0 (Hashtbl.find_opt context.declared holder) in
  List.exists
    (fun use -> reachable context ~earlier:at ~later:use ~declared)
    (Option.value ~default:[] (Hashtbl.find_opt context.uses holder))

(* Flow *)

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

(* Walking *)

type position = Read_position | Owned_position | Mut_position

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
      | None -> compound state flow value)

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
  | Is { value = tested; _ } -> expression state flow tested
  | Prefix (_, inner) | Any inner | Echo inner | Parenthesized inner | Mode (_, inner) ->
      expression state flow inner
  | Range { start; stop; _ } -> (
      let flow = match start with Some start -> expression state flow start | None -> flow in
      match stop with Some stop -> expression state flow stop | None -> flow)
  | Member (base, _) -> expression state flow base
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
  | _ -> expression state flow value

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
      flow

and statement state (flow : flow) (written : statement) : flow =
  let context = state.context in
  match written.kind with
  | Expression value -> expression state flow value
  | Let { mutable_; pattern; value; else_; _ } ->
      let flow = if mutable_ then owned_value state flow value else expression state flow value in
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
      flow
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
        loop state flow body ~held:(Option.to_list held)
          ~held_mode:(match iterable.kind with Mode (Mut, _) -> T.Mut | _ -> T.Read)
          ()
      in
      state.parallel_bodies <- before;
      flow
  | While { condition; body; _ } ->
      let flow = expression state flow condition in
      loop state flow body ~held:[] ~held_mode:T.Read ~condition ()
  | Parallel body -> parallel state flow body
  | Proof _ -> flow
  | Assert value | Yield value -> expression state flow value
  | Statement_error -> flow

(* A loop's body runs until the moved places stop changing. A loop over a
   place lends it for the whole loop. *)
and loop state flow body ~held ~held_mode ?condition () =
  let frame = { breaks = None; continues = None } in
  state.loop_frames <- frame :: state.loop_frames;
  let views_before = state.views in
  (* The collection a loop goes over is lent for the loop: nothing in the
     body may change it, and with [mut], nothing may use it at all. *)
  let loans_before = state.loans in
  state.loans <- List.map (fun lent -> { lent; lent_mode = held_mode }) held @ loans_before;
  let rec iterate entry count =
    frame.continues <- None;
    let after = block state entry body in
    let after = join after frame.continues in
    let after =
      match condition with Some condition -> expression state after condition | None -> after
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

and bound_names (written : pattern) =
  let found = ref [] in
  let rec go (written : pattern) =
    match written.kind with
    | Binding_or_constant name -> found := name.id :: !found
    | Variant { fields = Some fields; _ } | Record fields ->
        List.iter
          (fun (field : pattern_field) ->
            match field.kind with Named_field (_, inner) | Field inner -> go inner | Rest -> ())
          fields
    | Alternatives alternatives -> List.iter go alternatives
    | _ -> ()
  in
  go written;
  !found

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
                if
                  List.exists (fun read -> overlap read place = Overlap) others.reads
                  || List.exists
                       (fun (changed, _) -> overlap changed place = Overlap)
                       others.changes
                then
                  report context Parallel_conflict span
                    (Printf.sprintf
                       "One branch of this `parallel` block changes `%s`, which another branch \
                        uses."
                       (show_place context.names place)))
              effects.changes)
        branches)
    branches;
  flow

(* Preparing: what each local is, and where each is used *)

let prepare context =
  let paths = context.paths and loops = context.loops in
  let rec expression ~path ~loop_ids (value : expression) =
    Hashtbl.replace paths value.span.start path;
    Hashtbl.replace loops value.span.start loop_ids;
    (match value.kind with
    | Name name -> (
        match context.resolved.names.(name.last.id) with
        | Some (Local id) ->
            Hashtbl.replace context.uses id
              (value.span.start :: Option.value ~default:[] (Hashtbl.find_opt context.uses id))
        | _ -> ())
    | _ -> ());
    match value.kind with
    | If { condition; then_; else_ } ->
        expression ~path ~loop_ids condition;
        block ~path:((value.id, 0) :: path) ~loop_ids then_;
        Option.iter
          (function
            | Else other -> block ~path:((value.id, 1) :: path) ~loop_ids other
            | Else_if other -> expression ~path:((value.id, 1) :: path) ~loop_ids other)
          else_
    | Match { scrutinees; arms } ->
        List.iter (expression ~path ~loop_ids) scrutinees;
        (* What a pattern binds follows the matched value's mode: an owned
           value's parts are owned, a place's are views of it. *)
        let kinds =
          List.map
            (fun (scrutinee : expression) ->
              match scrutinee.kind with
              | Mode (Own, _) -> Owned
              | Mode (Mut, _) -> Mut_access
              | _ -> if place_of context scrutinee <> None then Viewing else Owned)
            scrutinees
        in
        List.iteri
          (fun index (arm : arm) ->
            let path = (value.id, index) :: path in
            if List.length arm.patterns = List.length kinds then
              List.iter2 (fun kind written -> bind ~kind written) kinds arm.patterns
            else List.iter (pattern ~path ~loop_ids) arm.patterns;
            Option.iter (expression ~path ~loop_ids) arm.guard;
            statement ~path ~loop_ids arm.body)
          arms
    | Is { value = tested; pattern = written; _ } ->
        expression ~path ~loop_ids tested;
        pattern ~path ~loop_ids written
    | Lambda { parameters; body } ->
        List.iter (pattern ~path ~loop_ids) parameters;
        block ~path ~loop_ids body
    | _ ->
        Syntax_walk.expression_parts ~expression:(expression ~path ~loop_ids)
          ~statement:(statement ~path ~loop_ids) value
  and statement ~path ~loop_ids (written : statement) =
    Hashtbl.replace paths written.span.start path;
    Hashtbl.replace loops written.span.start loop_ids;
    match written.kind with
    | Let { mutable_; pattern = written_pattern; value; else_; _ } ->
        expression ~path ~loop_ids value;
        Option.iter (block ~path ~loop_ids) else_;
        let kind =
          if mutable_ then Owned
          else
            match value.kind with
            | Mode (Own, _) -> Owned
            | _ -> if place_of context value <> None then Viewing else Owned
        in
        bind ~kind written_pattern
    | For { pattern = written_pattern; iterable; body; _ } ->
        expression ~path ~loop_ids iterable;
        let loop_ids = written.id :: loop_ids in
        let kind =
          match iterable.kind with
          | Mode (Mut, _) -> Mut_access
          | Mode (Own, _) -> Owned
          | _ -> Viewing
        in
        bind ~kind written_pattern;
        block ~path ~loop_ids body
    | While { condition; body; _ } ->
        let loop_ids = written.id :: loop_ids in
        expression ~path ~loop_ids condition;
        block ~path ~loop_ids body
    | _ ->
        Syntax_walk.statement_parts ~expression:(expression ~path ~loop_ids)
          ~statement:(statement ~path ~loop_ids) written
  and block ~path ~loop_ids (written : block) =
    List.iter (statement ~path ~loop_ids) written.statements
  and pattern ~path ~loop_ids written = bind ~kind:Viewing written
  and bind ~kind (written : pattern) =
    List.iter
      (fun id ->
        if not (Hashtbl.mem context.kinds id) then Hashtbl.replace context.kinds id kind;
        Hashtbl.replace context.declared id written.span.start)
      (bound_names written)
  in
  let bodies =
    match context.definition.kind with
    | Function { body; _ } | Test { body; _ } | Theorem { body; _ } | Law_proof { body; _ } ->
        [ body ]
    | Impl { members; _ } ->
        List.filter_map
          (fun (line : impl_member line) ->
            match line.kind with Impl_method { body; _ } -> Some body | _ -> None)
          members
    | Trait { members; _ } ->
        List.filter_map
          (fun (line : trait_member line) ->
            match line.kind with Trait_method { body; _ } -> body | _ -> None)
          members
    | _ -> []
  in
  List.iter (block ~path:[] ~loop_ids:[]) bodies

(* [lends]: one [yield] on every path *)

type count = Zero | One | Many

let add left right = match (left, right) with Zero, other | other, Zero -> other | _ -> Many

let lends_count context (body : block) ~report_span =
  let finished = ref [] in
  let rec block counts (written : block) = List.fold_left statement counts written.statements
  and statement counts (written : statement) =
    match written.kind with
    | Yield _ -> List.map (fun count -> add count One) counts
    (* A path that reaches [todo] is unfinished, not wrong. *)
    | Expression { kind = Todo; _ } -> List.map (fun _ -> One) counts
    | Expression value -> diverges value (expression counts value)
    | Let { value; _ } -> diverges value (expression counts value)
    | For { body; _ } | While { body; _ } ->
        if block [ Zero ] body <> [ Zero ] then
          List.concat_map (fun count -> [ count; add count Many ]) counts
        else counts
    | _ -> counts
  and expression counts (value : expression) =
    match value.kind with
    | If { then_; else_; _ } ->
        let then_counts = block counts then_ in
        let else_counts =
          match else_ with
          | Some (Else other) -> block counts other
          | Some (Else_if other) -> expression counts other
          | None -> counts
        in
        List.sort_uniq compare (then_counts @ else_counts)
    | Match { arms; _ } ->
        List.sort_uniq compare (List.concat_map (fun (arm : arm) -> statement counts arm.body) arms)
    | Return _ ->
        finished := counts @ !finished;
        []
    | Block written -> block counts written
    | _ -> counts
  (* A path through code of type [Never], such as [unreachable] or a call to
     [crash], never reaches the end, so it yields nothing there. *)
  and diverges (value : expression) counts =
    match context.checked.types.(value.id) with Some T.Never -> [] | _ -> counts
  in
  let ends = block [ Zero ] body @ !finished in
  if List.mem Zero ends then
    report context Lends_count report_span
      "A path through this lending method never yields. It must yield exactly once on every path."
  else if List.mem Many ends then
    report context Lends_count report_span
      "A path through this lending method yields more than once. It must yield exactly once on \
       every path."

(* Pullability, the one fact callers read from a body *)

(* The [yields] methods a method yields through: those a [for] loop in its
   body drives with a [yield] somewhere inside the loop. *)
let yields_through =
  Query.query ~name:"yields_through" ~show:Path.show (fun database (path : Path.t) ->
      match Interface.Summary.definition database path with
      | Some (key, { kind = Function { body; _ }; _ }) -> (
          match Query.demand database Infer.checked key with
          | Some result ->
              let contains_yield (loop_body : block) =
                let found = ref false in
                let rec statement (written : statement) =
                  (match written.kind with Yield _ -> found := true | _ -> ());
                  Syntax_walk.statement_parts ~expression ~statement written
                and expression value = Syntax_walk.expression_parts ~expression ~statement value in
                List.iter statement loop_body.statements;
                !found
              in
              let through = ref [] in
              let rec statement (written : statement) =
                (match written.kind with
                | For { iterable; body = loop_body; _ } when contains_yield loop_body -> (
                    let driven =
                      match result.checked.loops.(written.id) with
                      | Some (Yielding { call = { callee = Function { path; _ }; _ }; _ }) ->
                          Some path
                      | _ -> (
                          match result.checked.calls.(iterable.id) with
                          | Some { callee = Function { path; _ }; _ } -> Some path
                          | _ -> None)
                    in
                    match driven with Some driven -> through := driven :: !through | None -> ())
                | _ -> ());
                Syntax_walk.statement_parts ~expression ~statement written
              and expression value = Syntax_walk.expression_parts ~expression ~statement value in
              List.iter statement body.statements;
              List.sort_uniq Path.compare !through
          | None -> [])
      | _ -> [])

(* A [yields] method in its own cycle of yielding through, as a tree's
   [each] that loops over its subtrees, cannot be pulled: its cursor would
   need a stack of its own. *)
let pullable =
  Query.query ~name:"pullable" ~show:Path.show (fun database (path : Path.t) ->
      let rec reaches visited = function
        | [] -> false
        | next :: rest ->
            if Path.equal next path then true
            else if List.exists (Path.equal next) visited then reaches visited rest
            else reaches (next :: visited) (Query.demand database yields_through next @ rest)
      in
      not (reaches [] (Query.demand database yields_through path)))

(* A pull, [next()] on a cursor, of a method that cannot be pulled. *)
let check_pulls context =
  Array.iteri
    (fun id call ->
      match call with
      | Some
          { C.callee = Trait_method { name = "next"; self_type = T.Cursor { method_; _ }; _ }; _ }
        ->
          (match Query.demand context.database Interface.Environment.signature method_ with
          | Some { output = Yields (Mut, _); _ } ->
              Option.iter
                (fun (value : expression) ->
                  report context Not_pullable value.span
                    "A method that yields `mut` access cannot be pulled, since a cursor would \
                     store that access.")
                (find_expression context id)
          | _ -> ());
          if not (Query.demand context.database pullable method_) then
            Option.iter
              (fun (value : expression) ->
                report context Not_pullable value.span
                  (Printf.sprintf
                     "`%s` yields through a recursive loop, so it can drive a `for` loop but \
                      cannot be pulled. A cursor over it is a type with its own stack."
                     (Path.show method_)))
              (find_expression context id)
      | _ -> ())
    context.checked.calls

(* The check *)

type result = { diagnostics : Diagnostic.t list; moves : id list; obligations : C.obligation list }

(* The receiver a written signature declares. *)
let receiver_of (written : signature) : Path.receiver =
  match
    List.find_map
      (fun (parameter : parameter) ->
        match parameter.kind with Self_parameter mode -> Some mode | _ -> None)
      written.parameters
  with
  | None -> Static
  | Some None -> Read
  | Some (Some Mut) -> Mut
  | Some (Some Own) -> Own

let name_of (written : signature) =
  match written.name with Plain_name name | Member_name (_, name) -> name

(* Sets up the context for one body: its parameters' modes, which the
   lowered signature gives, and [self]'s. *)
let enter context (written : signature) (lowered : T.signature option) =
  let named =
    match lowered with
    | Some lowered ->
        List.filter_map
          (fun (parameter : parameter) ->
            match parameter.kind with
            | Named_parameter { name; _ } ->
                Option.map
                  (fun (info : T.parameter_info) -> (name.id, info.mode))
                  (List.find_opt
                     (fun (info : T.parameter_info) -> info.name = name.text)
                     lowered.parameters)
            | _ -> None)
          written.parameters
    | None -> []
  in
  List.iter
    (fun (id, mode) ->
      Hashtbl.replace context.kinds id
        (match mode with T.Own -> Owned | Mut -> Mut_access | Read -> Viewing))
    named;
  context.parameters <- List.map fst named;
  context.mutable_parameters <-
    List.filter_map (fun (id, mode) -> if mode = T.Mut then Some id else None) named;
  context.self_kind <-
    (match receiver_of written with
    | Own -> Some Owned
    | Mut -> Some Mut_access
    | Read -> Some Viewing
    | Static -> None)

let check database (key : Resolve.Names.key) =
  match
    ( Query.demand database Resolve.Names.definition key,
      Query.demand database Resolve.resolved key,
      Query.demand database Infer.checked key,
      Query.demand database Interface.Environment.lowered key )
  with
  | Some definition, Some resolved, Some checked, Some lowered ->
      let names = Hashtbl.create 32 in
      List.iter
        (fun (name : name) -> Hashtbl.replace names name.id name.text)
        (Syntax_walk.names definition);
      let nodes = Hashtbl.create 64 in
      let rec visit (value : expression) =
        Hashtbl.replace nodes value.id value;
        Syntax_walk.children visit value
      in
      Syntax_walk.definition visit definition;
      let context =
        {
          database;
          definition;
          resolved;
          checked = checked.checked;
          bounds =
            (fun parameter -> Option.value ~default:[] (List.assoc_opt parameter lowered.bounds));
          kinds = Hashtbl.create 32;
          names;
          nodes;
          parameters = [];
          mutable_parameters = [];
          self_kind = None;
          paths = Hashtbl.create 64;
          loops = Hashtbl.create 64;
          uses = Hashtbl.create 32;
          declared = Hashtbl.create 32;
          diagnostics = [];
          reported = [];
          moves = [];
          obligations = [];
          marks = Hashtbl.create 8;
        }
      in
      (* A function's, an [impl]'s, or a trait's method with a body: each
         with the signature its parameters' modes come from. *)
      let method_body (written : signature) lowered (body : block) =
        enter context written lowered;
        let state = new_state context in
        let flow = function_body state body in
        check_restored state flow body.span;
        match written.result with
        | Some (Lends _) -> lends_count context body ~report_span:(name_of written).span
        | _ -> ()
      in
      let find_method methods (written : signature) =
        List.find_map
          (fun (name, receiver, signature) ->
            if name = (name_of written).text && receiver = receiver_of written then Some signature
            else None)
          methods
      in
      if Option.is_some (Infer.clean database key) then begin
        prepare context;
        (match (definition.kind, lowered.interface) with
        | Function { body; signature = written }, Function_interface signature ->
            method_body written (Some signature) body
        | Function { body; signature = written }, _ -> method_body written None body
        | (Test { body; _ } | Theorem { body; _ } | Law_proof { body; _ }), _ ->
            ignore (block (new_state context) (Some []) body)
        | Impl { members; _ }, interface ->
            let methods =
              match interface with Impl_interface impl -> impl.impl_methods | _ -> []
            in
            List.iter
              (fun (line : impl_member line) ->
                match line.kind with
                | Impl_method { body; signature = written } ->
                    method_body written (find_method methods written) body
                | _ -> ())
              members
        | Trait { members; _ }, interface ->
            let methods =
              match interface with
              | Trait_interface trait ->
                  List.map
                    (fun (method_ : T.trait_method) ->
                      (method_.method_name, method_.method_receiver, method_.method_signature))
                    trait.methods
              | _ -> []
            in
            List.iter
              (fun (line : trait_member line) ->
                match line.kind with
                | Trait_method { body = Some body; signature = written } ->
                    method_body written (find_method methods written) body
                | _ -> ())
              members
        | _ -> ());
        check_pulls context
      end;
      Some
        {
          diagnostics =
            List.sort_uniq
              (fun (left : Diagnostic.t) (right : Diagnostic.t) ->
                compare (left.span, left.message) (right.span, right.message))
              context.diagnostics;
          moves = List.sort_uniq compare context.moves;
          obligations = List.rev context.obligations;
        }
  | _ -> None

let ownership = Query.query ~name:"ownership" ~show:Resolve.Names.show_key check

let diagnostics database module_ =
  Resolve.Names.per_definition database module_ (fun key ->
      match Query.demand database ownership key with
      | Some result -> result.diagnostics
      | None -> [])
