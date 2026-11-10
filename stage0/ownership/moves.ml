(* Moves, checked on the control-flow graph of a core form.

   A forward analysis finds, for each point, the places that may have been
   moved on some path to it. A use of a place that overlaps a moved place
   is an error. The rules on what may be moved need no flow: they depend
   on the place and on how its root is bound. *)

module T = Types
open Graph

(* How a local is bound: it owns its value, it views a place, or it has
   [mut] access to a place for a call, an iteration, or a block. *)
type kind = Owned | Viewing | Mut_access

type context = {
  database : Query.context;
  bounds : T.parameter -> T.trait_reference list;
  spans : Syntax.span array;
  text : string;  (** The definition's source text, in which the spans are offsets. *)
  names : (Core.local, string) Hashtbl.t;
  kinds : (Core.local, kind) Hashtbl.t;
  types : (Core.local, T.ty) Hashtbl.t;
  mutable parameters : Core.local list;
  mutable mut_parameters : Core.local list;
  mutable diagnostics : Diagnostic.t list;
  mutable moves : Core.id list;  (** The [Use] nodes that move a place. *)
  mutable disjoint : (Core.origin * Core.origin) list;
      (** Pairs of index calls or slices of one collection, by origin, that must select different
          elements, which the prover shows. *)
}

let plain context type_ = Interface.Impls.plain context.database ~bounds:context.bounds type_
let copyable context type_ = Interface.Impls.copyable context.database ~bounds:context.bounds type_
let is_view context type_ = Interface.Impls.is_view context.database ~bounds:context.bounds type_

let span context (origin : Core.origin) : Syntax.span =
  if origin >= 0 && origin < Array.length context.spans then context.spans.(origin)
  else Syntax.Span.make 0 0

let report context ?(fixes = []) ?(notes = []) code (at : Syntax.span) message =
  context.diagnostics <-
    Diagnostic.make ~fixes
      ~notes:
        (List.map
           (fun ((note : Syntax.span), text) -> (Source.span note.start note.stop, text))
           notes)
      ~code:(Ownership code) (Source.span at.start at.stop) message
    :: context.diagnostics

let kind_of_mode : T.mode -> kind = function Own -> Owned | Read -> Viewing | Mut -> Mut_access

let kind context (root : Place.root) =
  match root with
  | Constant _ -> Viewing
  | Local local -> Option.value ~default:Owned (Hashtbl.find_opt context.kinds local)

let show_root context (root : Place.root) =
  match root with
  | Local Self -> "self"
  | Local local -> Option.value ~default:"this" (Hashtbl.find_opt context.names local)
  | Constant (Top { name; _ } | Member_constant { name; _ }) -> name
  | Constant path -> Path.show path

let show context (place : Place.t) =
  show_root context place.root
  ^ String.concat ""
      (List.map (function Place.Field name -> "." ^ name | Element _ -> "[...]") place.steps)

(* The names and kinds of the definition's locals, from its parameters and
   its patterns. *)
let collect context (definition : Core.definition) =
  (match definition with
  | Function { parameters; _ } ->
      List.iter
        (fun (parameter : Core.parameter) ->
          Hashtbl.replace context.names parameter.local parameter.name;
          Hashtbl.replace context.kinds parameter.local (kind_of_mode parameter.mode);
          Hashtbl.replace context.types parameter.local parameter.type_;
          context.parameters <- parameter.local :: context.parameters;
          if parameter.mode = Mut && parameter.local <> Self then
            context.mut_parameters <- parameter.local :: context.mut_parameters)
        parameters
  | Type _ | Trait _ | Constant _ | Test _ | Law_proof _ | Empty -> ());
  Core_walk.definition
    {
      Core_walk.ignore_all with
      pattern =
        (fun (node : Core.pattern) ->
          match node.kind with
          | Bind { local; name; mode; _ } ->
              Hashtbl.replace context.names local name;
              Hashtbl.replace context.kinds local (kind_of_mode mode);
              Hashtbl.replace context.types local node.type_
          | _ -> ());
    }
    definition

(* Where the mark written before a place starts, if the place has that
   mark. The core form does not record marks, so this reads the source. *)
let mark_start context (place : Syntax.span) ~mark : int option =
  let rec skip_space index =
    if index > 0 && (context.text.[index - 1] = ' ' || context.text.[index - 1] = '\n') then
      skip_space (index - 1)
    else index
  in
  let stop = skip_space (min place.start (String.length context.text)) in
  let length = String.length mark in
  if stop < place.start && stop >= length && String.sub context.text (stop - length) length = mark
  then Some (stop - length)
  else None

(* The edits that copy at a move: [.copy()] after the place, and the [own]
   mark before it removed. *)
let copy_at context (moved : Syntax.span) =
  (match mark_start context moved ~mark:"own" with
    | Some start -> [ Diagnostic.delete (Source.span start moved.start) ]
    | None -> [])
  @ [ Diagnostic.insert moved.stop ".copy()" ]

(* The span of a place together with the [mut] or [own] mark before it. *)
let with_mark context (place : Syntax.span) : Syntax.span =
  match (mark_start context place ~mark:"mut", mark_start context place ~mark:"own") with
  | Some start, _ | None, Some start -> Syntax.Span.make start place.stop
  | None, None -> place

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
    | Mut_access, _ when place.steps = [] ->
        refuse
          (Printf.sprintf
             "`%s` is lent `mut`, so it cannot be moved away; a field of it can, if it is put back."
             shown)
    | (Owned | Mut_access), _ -> Moves

(* A moved place, with the point that moved it. *)
type moved = Place.t * int

let transfer verdicts (index : int) (point : point) (before : moved list) : moved list =
  match point.action with
  | Move { place; _ } when verdicts.(index) = Some Moves ->
      if List.mem (place, index) before then before else (place, index) :: before
  | Assign place -> List.filter (fun (moved, _) -> not (Place.is_prefix place moved)) before
  | Bind locals ->
      List.filter
        (fun ((moved : Place.t), _) ->
          match moved.root with Local local -> not (List.mem local locals) | Constant _ -> true)
        before
  | Enter | Read _ | Move _ | Take_lent _ | Mutate _ | Exit | Hold _ | Store _ | Return_view _
  | Views_temporary _ | Keeps_lent_part _ | Arguments _ ->
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
          (* A field moved out of a [mut] parameter must be assigned again
             before the function returns. *)
          List.iter
            (fun ((moved : Place.t), moved_at) ->
              match moved.root with
              | Local local when List.mem local context.mut_parameters ->
                  report context Field_not_restored at
                    ~notes:[ (span context points.(moved_at).origin, "It is moved out here.") ]
                    (Printf.sprintf
                       "`%s` belongs to the caller, so it must be given a value again before the \
                        function returns."
                       (show context moved))
              | _ -> ())
            before.(index)
      | Enter | Bind _ | Hold _ | Store _ | Return_view _ | Views_temporary _ | Keeps_lent_part _
      | Arguments _ ->
          ())
    points
