(* The control-flow graph of a definition's body, built from its MIR. Each
   point performs one action, and the edges follow the MIR's, so the order
   of evaluation is the MIR's. A lambda's body is a separate entry point: it
   runs when the lambda is called, not where it is made. Specifications and
   [proof] blocks are not in the graph, because they do not run. *)
(* A loan: a borrow of a place that lasts for a region of code. While a
   read-only loan is live, the place cannot be mutated. While a [mut] loan
   is live, the place cannot be used at all.

   - [Loop_body]: a loop borrows the collection that it iterates over.
   - [Provide_body]: a [provide] block borrows its implementations.
   - [Rest_of_statement]: a call of a lending method borrows its receiver
     until the statement ends.
   - [Operand_evaluation]: an evaluated operand stays borrowed until its
     operation runs, so that a later operand cannot mutate it. *)
type duration = Loop_body | Provide_body | Rest_of_statement | Operand_evaluation
type loan = { borrowed : Place.t; mode : Types.mode; duration : duration }

(* A place that a view-typed value may borrow from. *)
type view = {
  place : Place.t;
  copied_out : bool;
      (** If false, the value borrows [place] itself, as a slice of a list borrows the list. If
          true, the value is a copy of a view that is stored in [place], so it borrows the stored
          view's loans and not [place]. *)
}

(* An argument that is a place: the place, the parameter's mode, the
   argument's origin, and its position in the argument list. *)
type borrowed_argument = { place : Place.t; mode : Types.mode; at : Core.origin; position : int }

type action =
  | Enter  (** The start of a function's body, a test's body, or a lambda's body. *)
  | Read of Place.t  (** The place is read or borrowed read-only. *)
  | Move of {
      place : Place.t;
      use : Core.id;  (** The [Use] node that moves the value. *)
      type_ : Types.ty;
      returned : bool;  (** The moved value is the function's return value. *)
      captured : bool;
          (** The place is a local of an enclosing function, which the current lambda captures. *)
    }  (** A value that is not [Plain] is moved out of the place. *)
  | Move_out_of_lent of Types.ty
      (** A value that is not [Plain] is moved out of a part that a lending call lent. *)
  | Mutate of Place.t  (** The place is borrowed [mut]. *)
  | Assign of Place.t
  | Bind of Core.local list  (** A pattern binds these locals to new values. *)
  | Scope_end of Core.local list
      (** These locals go out of scope: a loop's pattern variables after the loop, a [match] arm's
          bindings after the arm, and a lambda's parameters at the end of its body. *)
  | Task_end of { first : int; limit : int }
      (** The end of a [concurrent] branch, whose points are [first] up to [limit], exclusive. If
          another branch exits the block early, the code after the block does not run. So by this
          point the branch must have reinitialized every place that it moved out of a [mut] borrow.
      *)
  | Yield_point of { mode : Types.mode; lent : Place.t option list; views : view list }
      (** A [yield]. The caller's loop may [break] here, in which case the method never resumes.
          [lent] is the places that the yield lends, where [None] is a place that the check does not
          track. [views] is the views of the yielded value, if it has a view type. *)
  | Exit  (** The function returns. *)
  | Bind_views of { locals : Core.local list; views : view list }
      (** A pattern binds [locals] to a value that has these views. *)
  | Store of { place : Place.t; views : view list }
      (** A value that has these views is stored in the place: by an assignment, or by a call that
          borrows the place [mut] and may store one of its view arguments there. *)
  | Return_view of view list  (** The function returns a value that has these views. *)
  | View_of_temporary of Place.t option
      (** A dangling view: a temporary is dropped when the statement ends, but a view of it is bound
          by the statement ([None]) or stored in the given place. The point's origin is the
          temporary. *)
  | Bind_lent_part of Types.ty
      (** A [let] binds a part that a lending call lent. The loan ends with the statement. *)
  | Pass_owned_function of view list
      (** A function value that has these views is passed to an [own] parameter. The callee may
          store the function, so the function could outlive its captures. *)
  | Write_through of Place.t
      (** A mutation writes through the slice that is stored in this place, so it mutates every
          place that the slice views. *)
  | Arguments of {
      places : borrowed_argument list;
      views : (int * view list * Core.origin) list;
      yielded : bool;
    }
      (** The places that one call borrows, in argument order, to be checked for aliasing. [views]
          lists each argument of a view type: its position, its views, and its origin. If [yielded],
          the places are those that a yielded constructor lends, and [views] is empty. *)

(* The points numbered [first] up to [limit], exclusive. Points are numbered
   in creation order, so the points of one statement are contiguous. *)
type range = { first : int; limit : int }

type point = {
  action : action;
  origin : Core.origin;
  loans : loan list;  (** The loans that are live at the point. *)
  mutable successors : int list;
}

type fork_join_block = { keyword : string; branches : range list }
(** A [parallel] or [concurrent] block: a fork-join of its branches, which may run at the same time.
    [keyword] is "parallel" or "concurrent", for error messages. *)

type fork_join_loop = { keyword : string; body : range; bound : Core.local list }
(** A [parallel for] or [concurrent for]: a fork-join of its iterations, which may run at the same
    time. [body] is the points of the loop body, and [bound] is the locals that the loop's pattern
    binds. *)

type t = {
  points : point array;
  entries : int list;  (** The [Enter] points: the definition's body first, then each lambda. *)
  fork_join_blocks : fork_join_block list;
  fork_join_loops : fork_join_loop list;
}

(* The builder *)

(* A point before its loans are known: the loans it starts or ends, which a
   forward pass turns into the loans live at each point. *)
type draft = {
  draft_action : action;
  draft_origin : Core.origin;
  mutable draft_successors : int list;
  starts : (int * loan list) option;
  ends : int list;
}

(* What the builder knows of a local of the MIR. *)
type held = {
  place : Place.t option;  (** The tracked place it is, for a lent part or an alias. *)
  views : view list;  (** The views of the value it holds, for a temporary. *)
  temporaries : Core.origin list;
      (** The owned temporaries the value it holds views, which end with their statement. *)
  slice : Place.t option;  (** For a slice, the elements it views. *)
  lent : Place.t option list;  (** For a constructed value, the places its fields lend. *)
  collection : (Place.t option * Types.ty) option;
      (** For an element of a collection, the collection and its type. *)
  fresh : bool;
      (** For a temporary, whether its value is a new one, which the statement drops: not a string
          literal, a lambda, or a value read out of a named place. *)
  alias : Mir.place option;  (** For an operand held where it is evaluated, the place it is. *)
  part : bool;  (** Whether it is the part a loop over a yielding call is given. *)
}

let nothing =
  {
    place = None;
    views = [];
    temporaries = [];
    slice = None;
    lent = [];
    collection = None;
    fresh = true;
    alias = None;
    part = false;
  }

type builder = {
  drafts : (int, draft) Hashtbl.t;
  mutable count : int;
  mutable entries : int list;
  mutable fork_join_blocks : fork_join_block list;
  mutable fork_join_loops : fork_join_loop list;
  plain : Types.ty -> bool;
  is_view : Types.ty -> bool;
  holds_function : Types.ty -> bool;
  stores_function : Mir.callee -> int -> bool;
  mutable body : Mir.body;
  mutable captured : Core.local list;
  mutable last : int option;  (** The point the next point follows. *)
  held : (Mir.local, held) Hashtbl.t;
  mutable returned : Mir.local list;  (** The temporaries whose value the body returns. *)
  mutable aliases : Mir.local list;
      (** The lent locals that an assignment made: an operand held where it is evaluated. *)
  mutable binding : Mir.local list;  (** The locals made live and not yet given a value. *)
  mutable storage_lend : bool;
      (** Whether the last lend was of an element of a collection, which lends nothing for the
          statement. *)
  mutable block : int;  (** The block being built. *)
  mutable keeps_lent : (Mir.local * Mir.local * Types.ty * Core.origin) list;
      (** Each binding of a lent part not yet dead: the binding, the part, its type, and where it is
          bound. A binding still live where its part ends would outlive the loan. *)
  loop_entries : (int, int) Hashtbl.t;
      (** For the first block of a loop's body, the first point after the loop's loan starts. *)
}

let add builder ?starts ?(ends = []) action origin =
  let id = builder.count in
  Hashtbl.replace builder.drafts id
    { draft_action = action; draft_origin = origin; draft_successors = []; starts; ends };
  builder.count <- id + 1;
  id

let link builder from target =
  let draft = Hashtbl.find builder.drafts from in
  if not (List.mem target draft.draft_successors) then
    draft.draft_successors <- target :: draft.draft_successors

(* Adds a point after the last, and makes it the last. *)
let emit builder ?starts ?ends action origin =
  let id = add builder ?starts ?ends action origin in
  Option.iter (fun last -> link builder last id) builder.last;
  builder.last <- Some id;
  id

let emit_ builder ?starts ?ends action origin = ignore (emit builder ?starts ?ends action origin)
let held builder local = Option.value ~default:nothing (Hashtbl.find_opt builder.held local)
let local_info builder local = builder.body.locals.(local)

(* The core local a local of the MIR is, if it is one. *)
let source builder (local : Mir.local) =
  match (local_info builder local).kind with
  | Source { local; _ } -> Some local
  | Temporary | Lent _ -> None

(* The tracked place a place of the MIR denotes: a source local's place, or
   the place a lent part or an alias is. A field of a variant is tracked as
   the whole value, since a test selected it. *)
let tracked builder (place : Mir.place) : Place.t option =
  let base =
    match place.root with
    | Constant path -> Some { Place.root = Constant path; steps = [] }
    | Local local -> (
        match source builder local with
        | Some local -> Some { Place.root = Local local; steps = [] }
        | None -> (held builder local).place)
  in
  Option.map
    (fun (base : Place.t) ->
      List.fold_left
        (fun (place : Place.t) (projection : Mir.projection) ->
          match projection with
          | Field field -> { place with steps = place.steps @ [ Field field ] }
          | Variant_field _ -> place)
        base place.projections)
    base

(* Whether a place is a part that a lending call lent other than an element
   of a [List], a [Slice], or an [Array]: such a part is not tracked. *)
let is_lent_part builder (place : Mir.place) =
  match place.root with
  | Local local -> (
      match (local_info builder local).kind with
      | Lent _ -> (held builder local).collection = None && (held builder local).place = None
      | Source _ | Temporary -> false)
  | Constant _ -> false

let is_temporary builder (place : Mir.place) =
  match place.root with
  | Local local -> (local_info builder local).kind = Temporary
  | Constant _ -> false

let rec temporary_of builder (place : Mir.place) =
  match place with
  | { root = Local local; _ } when (local_info builder local).kind = Temporary -> Some local
  | { root = Local local; _ } -> (
      match (held builder local).alias with
      | Some aliased -> temporary_of builder aliased
      | None -> None)
  | _ -> None

(* The views of a value read out of a place. *)
let views_of_copy builder (place : Mir.place) =
  match tracked builder place with
  | Some place -> [ { place; copied_out = true } ]
  | None -> ( match place.root with Local local -> (held builder local).views | Constant _ -> [])

(* The views of a borrow of a place: the place itself. A place of a [Plain]
   type is copied, not borrowed. *)
let views_of_borrow builder (place : Mir.place) type_ =
  match tracked builder place with
  | Some place -> [ { place; copied_out = builder.plain type_ } ]
  | None -> ( match place.root with Local local -> (held builder local).views | Constant _ -> [])

let operand_type : Mir.operand -> Types.ty option = function
  | Use { type_; _ } | Borrow { type_; _ } | Take { type_; _ } -> Some type_
  | Constant _ -> None

let views_of_operand builder (operand : Mir.operand) =
  match operand with
  | Use { place; _ } | Take { place; _ } -> views_of_copy builder place
  | Borrow { place; type_; _ } -> views_of_borrow builder place type_
  | Constant _ -> []

(* The views of a part of a value, if it has a view type. *)
let views_of_part builder (operand : Mir.operand) =
  match operand_type operand with
  | Some type_ when builder.is_view type_ -> views_of_operand builder operand
  | _ -> []

(* The places an operand depends on until its operation runs: the place it
   borrows, or the places its value views. *)
let operand_borrows builder (operand : Mir.operand) =
  match operand with
  | Borrow { place; _ } -> Option.to_list (tracked builder place)
  | Use { type_; _ } when builder.is_view type_ ->
      List.map (fun (view : view) -> view.place) (views_of_operand builder operand)
  | Use _ | Take _ | Constant _ -> []

(* Whether a call's result may be a view of an argument: the argument is
   borrowed and is not [Plain], or it is itself a view. *)
let result_may_view builder (mode : Types.mode) type_ =
  (mode <> Own && not (builder.plain type_)) || builder.is_view type_

let viewable_arguments builder (call : Mir.call) =
  List.filter_map
    (fun (argument : Mir.argument) ->
      match argument with
      | Passed { mode; value; _ } -> (
          match operand_type value with
          | Some type_ when result_may_view builder mode type_ -> Some value
          | _ -> None)
      | Default -> None)
    call.arguments

(* The owned temporaries an operand passed read-only views: a value with no
   name that the statement drops. *)
let owned_temporaries builder (mode : Types.mode) (operand : Mir.operand) =
  match operand with
  | (Borrow { place; type_; _ } | Use { place; type_; _ }) when mode = Read -> (
      match temporary_of builder place with
      | Some local when not (builder.plain type_) ->
          if builder.is_view type_ then (held builder local).temporaries
          else if (held builder local).fresh then [ (local_info builder local).origin ]
          else []
      | _ -> [])
  | Use { place; type_; _ } when builder.is_view type_ -> (
      match place.root with Local local -> (held builder local).temporaries | Constant _ -> [])
  | _ -> []

(* The slice that a mutation of a place writes through, if any: the place
   itself where it is a slice borrowed [mut] whole, or the innermost slice
   whose element the place is. *)
let written_slice builder ~whole (place : Mir.place) type_ =
  if whole && Place.is_slice_type type_ then tracked builder place
  else
    match place.root with
    | Local local -> (
        match (held builder local).collection with
        | Some (collection, collection_type) when Place.is_slice_type collection_type -> collection
        | _ -> None)
    | Constant _ -> None

let writes_through builder ~whole (place : Mir.place) type_ origin =
  Option.iter
    (fun slice -> emit_ builder (Write_through slice) origin)
    (written_slice builder ~whole place type_)

(* Actions *)

let is_captured builder (place : Place.t) =
  match place.root with
  | Local local -> List.mem local builder.captured
  | Constant _ | Environment -> false

(* The value at a place is read: copied, or moved out of it. *)
let use builder (place : Mir.place) type_ node origin ~returned =
  match tracked builder place with
  | Some tracked ->
      if builder.plain type_ then emit_ builder (Read tracked) origin
      else
        emit_ builder
          (Move
             {
               place = tracked;
               use = node;
               type_;
               returned;
               captured = is_captured builder tracked;
             })
          origin
  | None ->
      if is_lent_part builder place && not (builder.plain type_) then
        emit_ builder (Move_out_of_lent type_) origin

(* An operand is evaluated: a value is read, and a read-only borrow reads
   the place. A [mut] borrow starts where its operation runs. *)
let evaluate builder ?(returned = false) (operand : Mir.operand) =
  match operand with
  | Use { place; type_; node; origin } -> use builder place type_ node origin ~returned
  | Borrow { place; mode = Read | Own; origin; _ } -> (
      match place.root with
      | Local local when List.mem local builder.aliases -> ()
      | _ ->
          Option.iter (fun tracked -> emit_ builder (Read tracked) origin) (tracked builder place))
  | Take { place; origin; _ } ->
      Option.iter (fun tracked -> emit_ builder (Read tracked) origin) (tracked builder place)
  | Borrow { mode = Mut; _ } | Constant _ -> ()

(* The [mut] borrow of an operand. *)
let borrow_mut builder (operand : Mir.operand) =
  match operand with
  | Borrow { place; type_; mode = Mut; origin } ->
      writes_through builder ~whole:true place type_ origin;
      Option.iter (fun tracked -> emit_ builder (Mutate tracked) origin) (tracked builder place)
  | Use { place; origin; _ } -> (
      match place.root with
      | Local local ->
          Option.iter (fun slice -> emit_ builder (Mutate slice) origin) (held builder local).slice
      | Constant _ -> ())
  | _ -> ()

(* Stores views in a place. None of them may be a view of a temporary,
   which is dropped when the statement ends. *)
let store_views builder (place : Place.t) origin ~views ~temporaries =
  List.iter (fun origin -> emit_ builder (View_of_temporary (Some place)) origin) temporaries;
  emit_ builder (Store { place; views }) origin

(* A call: what it reads, its [mut] borrows, the aliasing of what it
   borrows, the views it may store in a [mut] argument, and the functions it
   may keep. *)
let call builder (call : Mir.call) origin =
  (match call.callee with Indirect value -> evaluate builder value | _ -> ());
  let passed =
    List.filter_map
      (function Mir.Passed { mode; value; _ } -> Some (mode, value) | Default -> None)
      call.arguments
  in
  List.iter (fun (_, value) -> evaluate builder value) passed;
  List.iter (fun (mode, value) -> if mode = Types.Mut then borrow_mut builder value) passed;
  let places =
    List.concat
      (List.mapi
         (fun position (argument : Mir.argument) ->
           match argument with
           | Passed { mode; value = Borrow { place; origin; _ }; _ } -> (
               match tracked builder place with
               | Some place -> [ { place; mode; at = origin; position } ]
               | None -> [])
           | Passed { mode = Mut; value = Use { place = { root = Local local; _ }; origin; _ }; _ }
             -> (
               match (held builder local).slice with
               | Some place -> [ { place; mode = Mut; at = origin; position } ]
               | None -> [])
           | Passed _ | Default -> [])
         call.arguments)
  in
  let views =
    match call.callee with
    | Intrinsic { operation = Storage_take_view | View_take_view | Array_take_view; _ } -> []
    | _ ->
        List.concat
          (List.mapi
             (fun position (argument : Mir.argument) ->
               match argument with
               | Passed
                   { value = (Use { type_; origin; _ } | Borrow { type_; origin; _ }) as value; _ }
                 when builder.is_view type_ ->
                   [ (position, views_of_operand builder value, origin) ]
               | Passed _ | Default -> [])
             call.arguments)
  in
  if List.length places > 1 || (places <> [] && views <> []) then
    emit_ builder (Arguments { places; views; yielded = false }) origin;
  let can_store_in target (other : Mir.operand) =
    match operand_type other with
    | Some (Types.Function { output = Returns output; _ }) when not (builder.is_view output) ->
        builder.holds_function target
    | _ -> true
  in
  List.iter
    (fun (argument : Mir.argument) ->
      match argument with
      | Passed { mode = Mut; value = Borrow { place; type_; _ } as target; _ }
        when builder.is_view type_ -> (
          match tracked builder place with
          | Some place ->
              let others =
                List.filter
                  (fun other ->
                    other != target
                    && (match operand_type other with Some t -> builder.is_view t | None -> false)
                    && can_store_in type_ other)
                  (viewable_arguments builder call)
              in
              store_views builder place origin
                ~views:(List.concat_map (views_of_operand builder) others)
                ~temporaries:(List.concat_map (owned_temporaries builder Own) others)
          | None -> ())
      | _ -> ())
    call.arguments;
  List.iteri
    (fun position (argument : Mir.argument) ->
      match argument with
      | Passed { mode = Own; value = Use { type_ = Types.Function _; origin; _ } as value; _ }
        when builder.stores_function call.callee position ->
          emit_ builder (Pass_owned_function (views_of_operand builder value)) origin
      | _ -> ())
    call.arguments

(* What a call's result holds: views of the arguments it may view. *)
let call_result builder (call : Mir.call) =
  let viewable = viewable_arguments builder call in
  {
    nothing with
    views = List.concat_map (views_of_operand builder) viewable;
    temporaries =
      List.concat_map
        (fun (argument : Mir.argument) ->
          match argument with
          | Passed { mode; value; _ } -> owned_temporaries builder mode value
          | Default -> [])
        call.arguments;
  }

let hold builder (place : Mir.place) (value : held) =
  match place with
  | { root = Local local; projections = [] } ->
      let known = held builder local in
      Hashtbl.replace builder.held local
        {
          place = (match value.place with Some _ -> value.place | None -> known.place);
          views =
            known.views @ List.filter (fun view -> not (List.mem view known.views)) value.views;
          temporaries = known.temporaries @ value.temporaries;
          slice = (match value.slice with Some _ -> value.slice | None -> known.slice);
          lent = (match value.lent with [] -> known.lent | lent -> lent);
          collection =
            (match value.collection with Some _ -> value.collection | None -> known.collection);
          fresh = known.fresh && value.fresh;
          alias = (match value.alias with Some _ -> value.alias | None -> known.alias);
          part = known.part || value.part;
        }
  | _ -> ()

(* The places a yielded or constructed value lends: its fields that are
   borrows, to any depth. *)
let lent_places builder (operand : Mir.operand) =
  match operand with
  | Borrow { place; _ } -> [ tracked builder place ]
  | Use { place = { root = Local local; projections = [] }; _ }
    when (local_info builder local).kind = Temporary ->
      (held builder local).lent
  | Use _ | Take _ | Constant _ -> []

(* What an rvalue reads, and what its value holds. *)
let rvalue builder (value : Mir.rvalue) origin : held =
  match value with
  | Operand operand ->
      evaluate builder operand;
      let views = views_of_operand builder operand in
      let temporaries =
        match operand with
        | Use { place = { root = Local local; _ }; _ } -> (held builder local).temporaries
        | _ -> []
      in
      let lent = lent_places builder operand in
      let slice, fresh =
        match operand with
        | Use { place = { root = Local local; _ } as place; _ } when is_temporary builder place ->
            ((held builder local).slice, (held builder local).fresh)
        | Use _ | Take _ | Borrow _ -> (None, false)
        | Constant _ -> (None, false)
      in
      {
        nothing with
        views;
        temporaries;
        lent = (match operand with Borrow _ -> [] | _ -> lent);
        slice;
        fresh;
      }
  | Operation { operands; _ } ->
      List.iter (evaluate builder) operands;
      nothing
  | Compare { left; right; _ } ->
      evaluate builder left;
      evaluate builder right;
      nothing
  | Not operand | Convert { value = operand; _ } | To_any { value = operand; _ } | Copy operand ->
      evaluate builder operand;
      let temporaries =
        match operand with
        | Use { place = { root = Local local; _ } as place; _ } when is_temporary builder place ->
            (held builder local).temporaries
        | _ -> []
      in
      { nothing with views = views_of_operand builder operand; temporaries }
  | Construct { fields; _ } ->
      let given = List.filter_map snd fields in
      List.iter
        (fun field -> match field with Mir.Borrow _ -> () | _ -> evaluate builder field)
        given;
      {
        nothing with
        views =
          List.concat_map
            (fun (field : Mir.operand) ->
              match field with
              | Borrow { place; type_; _ } -> views_of_borrow builder place type_
              | _ -> views_of_part builder field)
            given;
        temporaries =
          List.concat_map
            (fun field ->
              match field with Mir.Borrow _ -> [] | _ -> owned_temporaries builder Own field)
            given;
        lent = List.concat_map (lent_places builder) given;
      }
  | Array elements ->
      List.iter (evaluate builder) elements;
      { nothing with views = List.concat_map (views_of_part builder) elements }
  | Is_variant { place; _ } ->
      Option.iter (fun tracked -> emit_ builder (Read tracked) origin) (tracked builder place);
      nothing
  | Lambda { captures; _ } -> (
      List.iter
        (fun (capture : Core.capture) ->
          emit_ builder (Read { root = Local capture.local; steps = [] }) origin)
        captures;
      match captures with
      | [] -> { nothing with fresh = false }
      | _ ->
          {
            nothing with
            fresh = false;
            views =
              { place = { root = Environment; steps = [] }; copied_out = false }
              :: List.map
                   (fun (capture : Core.capture) ->
                     { place = { root = Local capture.local; steps = [] }; copied_out = false })
                   captures;
          })
  | Function_value _ | Value_parameter _ -> nothing

(* A local the body is about to bind: its first assignment is its value. *)
let bound_value builder (local : Mir.local) (core : Core.local) (value : Mir.rvalue) origin ~is_var
    =
  let type_ = (local_info builder local).type_ in
  let holds_views =
    builder.is_view type_ || match type_ with Types.Cursor _ -> true | _ -> false
  in
  let result = rvalue builder value origin in
  (match value with
  | Operand
      (Borrow { place = { root = Local part; _ } as place; type_ = part_type; origin = at; _ })
    when (not is_var) && is_lent_part builder place
         && ((not (builder.plain part_type)) || builder.is_view part_type) ->
      builder.keeps_lent <- (local, part, part_type, at) :: builder.keeps_lent
  | _ -> ());
  let views =
    match value with
    | Operand (Borrow { place; type_ = part_type; _ })
      when holds_views || is_temporary builder place
           || (Option.is_some (tracked builder place) && not (builder.plain part_type)) ->
        views_of_borrow builder place part_type
    | Operand (Borrow _) -> []
    | _ when holds_views -> result.views
    | _ -> []
  in
  (* A loop's variable of a [Plain] type holds a copy of the element, so it
     has only the element's own views. *)
  let from_part =
    match value with
    | Operand
        ( Use { place = { root = Local part; _ }; _ }
        | Borrow { place = { root = Local part; _ }; _ } ) ->
        (held builder part).part
    | _ -> false
  in
  let views =
    if from_part && builder.plain type_ then
      List.map (fun (view : view) -> { view with copied_out = true }) views
    else views
  in
  if holds_views then
    List.iter (fun at -> emit_ builder (View_of_temporary None) at) result.temporaries;
  if holds_views || views <> [] then emit_ builder (Bind_views { locals = [ core ]; views }) origin

let returned_temporaries (body : Mir.body) =
  let returned = ref [] in
  Array.iter
    (fun (block : Mir.basic_block) ->
      match block.terminator with
      | Return (Some (Use { place = { root = Local local; projections = [] }; _ }))
      | Exit_tasks
          {
            exit = Exit_return (Some (Use { place = { root = Local local; projections = [] }; _ }));
            _;
          }
        when body.locals.(local).kind = Temporary ->
          returned := local :: !returned
      | _ -> ())
    body.blocks;
  let changed = ref true in
  while !changed do
    changed := false;
    Array.iter
      (fun (block : Mir.basic_block) ->
        List.iter
          (fun (statement : Mir.statement) ->
            match statement.kind with
            | Assign
                {
                  target = { root = Local target; projections = [] };
                  value = Operand (Use { place = { root = Local source; projections = [] }; _ });
                  _;
                }
              when List.mem target !returned
                   && body.locals.(source).kind = Temporary
                   && not (List.mem source !returned) ->
                returned := source :: !returned;
                changed := true
            | _ -> ())
          block.statements)
      body.blocks
  done;
  !returned

(* The loans one [Loan_start] starts. *)
let loans_of builder (borrowed : Mir.operand) mode (duration : Mir.loan_duration) : loan list =
  let duration : duration =
    match duration with
    | Loop_body -> Loop_body
    | Provide_body -> Provide_body
    | Rest_of_statement -> Rest_of_statement
    | Operand_evaluation -> Operand_evaluation
  in
  List.map (fun borrowed : loan -> { borrowed; mode; duration }) (operand_borrows builder borrowed)

type fork = { concurrent : bool; mutable branches : range list; mutable first : int }

let statement builder (forks : (int, fork) Hashtbl.t) ~is_var (statement : Mir.statement) =
  let origin = statement.origin in
  match statement.kind with
  | Live locals ->
      builder.binding <- locals @ builder.binding;
      let core = List.filter_map (source builder) locals in
      if core <> [] then emit_ builder (Bind core) origin
  | Dead locals ->
      List.iter
        (fun (binding, part, part_type, at) ->
          if List.mem part locals && not (List.mem binding locals) then
            emit_ builder (Bind_lent_part part_type) at)
        builder.keeps_lent;
      builder.keeps_lent <-
        List.filter
          (fun (binding, part, _, _) -> not (List.mem binding locals || List.mem part locals))
          builder.keeps_lent;
      let core = List.filter_map (source builder) locals in
      if core <> [] then emit_ builder (Scope_end core) origin
  | Assign { target = { root = Local local; projections = [] } as target; value; _ }
    when List.mem local builder.binding
         ||
         match (local_info builder local).kind with
         | Temporary -> true
         | Lent _ -> not (Hashtbl.mem builder.held local)
         | Source _ -> false -> (
      builder.binding <- List.filter (fun bound -> bound <> local) builder.binding;
      match (local_info builder local).kind with
      | Temporary -> (
          match value with
          | Operand (Use { place; type_; node; origin = at })
            when List.mem local builder.returned && Option.is_some (tracked builder place) ->
              use builder place type_ node at ~returned:true;
              hold builder target { nothing with views = views_of_copy builder place }
          | _ -> hold builder target (rvalue builder value origin))
      | Lent _ -> (
          builder.aliases <- local :: builder.aliases;
          let result = rvalue builder value origin in
          match value with
          | Operand (Borrow { place; _ }) ->
              hold builder target
                {
                  nothing with
                  place = tracked builder place;
                  views = result.views;
                  alias = Some place;
                  fresh = false;
                }
          | _ -> hold builder target result)
      | Source { local = core; _ } ->
          bound_value builder local core value origin ~is_var:(is_var core))
  | Assign { target; value; _ } -> (
      let result = rvalue builder value origin in
      match tracked builder target with
      | Some place -> (
          let type_ = match value with Operand operand -> operand_type operand | _ -> None in
          writes_through builder ~whole:false target (Option.value ~default:Types.unit type_) origin;
          emit_ builder (Assign place) origin;
          match type_ with
          | Some type_ when builder.is_view type_ ->
              store_views builder place origin ~views:result.views ~temporaries:result.temporaries
          | _ -> ())
      | None -> hold builder { target with projections = [] } result)
  | Call { destination; call = called } ->
      call builder called origin;
      Option.iter
        (fun destination -> hold builder destination (call_result builder called))
        destination
  | Template { destination; call = called; _ } ->
      call builder called origin;
      hold builder destination (call_result builder called)
  | Lend { part; call = called } -> (
      let element =
        match (called.callee, called.arguments) with
        | ( Trait_method { trait; name = "at"; self_type; _ },
            Passed { value = Borrow { place = collection; type_ = collection_type; _ }; _ } :: _ )
          when Well_known.is Index trait.trait
               && (Types.is_well_known List self_type
                  || Types.is_well_known Slice self_type
                  || Types.is_builtin Array self_type) ->
            let collection_place = tracked builder collection in
            Some
              ( Option.map
                  (fun (place : Place.t) ->
                    { place with steps = place.steps @ [ Element { node = called.node; origin } ] })
                  collection_place,
                (collection_place, collection_type) )
        | _ -> None
      in
      match element with
      | Some (place, collection) ->
          (* An element of a [List], a [Slice], or an [Array] is a place of
             its own: the index reads the collection, and lends no part of
             it for the statement. *)
          List.iter
            (fun (argument : Mir.argument) ->
              match argument with Passed { value; _ } -> evaluate builder value | Default -> ())
            (List.tl called.arguments);
          builder.storage_lend <- true;
          hold builder
            { Mir.root = Local part; projections = [] }
            { nothing with place; collection = Some collection }
      | None ->
          call builder called origin;
          hold builder { Mir.root = Local part; projections = [] } (call_result builder called))
  | Slice { destination; base; call = called } ->
      call builder called origin;
      let base_type =
        match called.arguments with
        | Passed { value = Borrow { type_; _ }; _ } :: _ -> Some type_
        | _ -> None
      in
      let elements =
        Option.map
          (fun (place : Place.t) ->
            { place with steps = place.steps @ [ Element { node = called.node; origin } ] })
          (tracked builder base)
      in
      let views =
        match elements with
        | Some place ->
            [
              {
                place;
                copied_out =
                  (match base_type with Some t -> Place.is_slice_type t | None -> false);
              };
            ]
        | None -> views_of_borrow builder base (Option.value ~default:Types.unit base_type)
      in
      let temporaries =
        match temporary_of builder base with
        | Some local
          when (held builder local).fresh
               && not (builder.plain (Option.value ~default:Types.unit base_type)) ->
            [ (local_info builder local).origin ]
        | _ -> []
      in
      hold builder destination { nothing with views; slice = elements; temporaries }
  | Pull { destination; cursor } ->
      Option.iter (fun tracked -> emit_ builder (Mutate tracked) origin) (tracked builder cursor);
      hold builder destination { nothing with views = views_of_copy builder cursor }
  | Assert value | Echo value -> evaluate builder value
  | Provide { provided; _ } ->
      List.iter
        (fun (provided : Mir.provided) ->
          evaluate builder provided.value;
          if provided.mode = Mut then borrow_mut builder provided.value)
        provided
  | Loan_start { loan; borrowed; mode; duration } ->
      let loans =
        if duration = Rest_of_statement && builder.storage_lend then []
        else loans_of builder borrowed mode duration
      in
      builder.storage_lend <- false;
      (* A loop that borrows its collection [mut] may change it on every
         iteration. *)
      if duration = Loop_body && mode = Mut then
        List.iter (fun (loan : loan) -> emit_ builder (Mutate loan.borrowed) origin) loans;
      emit_ builder ~starts:(loan, loans) (Bind []) origin;
      if duration = Loop_body then Hashtbl.replace builder.loop_entries builder.block builder.count
  | Loan_end loans -> emit_ builder ~ends:loans (Bind []) origin
  | Fork_start { fork; concurrent } ->
      (match Hashtbl.find_opt forks fork with
      | Some open_fork ->
          if open_fork.concurrent then
            emit_ builder (Task_end { first = open_fork.first; limit = builder.count }) origin;
          open_fork.branches <-
            open_fork.branches @ [ { first = open_fork.first; limit = builder.count } ];
          open_fork.first <- builder.count
      | None -> Hashtbl.replace forks fork { concurrent; branches = []; first = builder.count });
      emit_ builder (Bind []) origin
  | Fork_end { fork } -> (
      match Hashtbl.find_opt forks fork with
      | Some open_fork ->
          let limit = builder.count in
          if open_fork.concurrent then
            emit_ builder (Task_end { first = open_fork.first; limit }) origin;
          builder.fork_join_blocks <-
            {
              keyword = (if open_fork.concurrent then "concurrent" else "parallel");
              branches = open_fork.branches @ [ { first = open_fork.first; limit } ];
            }
            :: builder.fork_join_blocks;
          Hashtbl.remove forks fork
      | None -> ())
  | Provide_end | Ghost_assert _ | Matched _ | Proof _ -> ()

(* The points of a body: one run of points for each block, linked as its
   terminator jumps. *)
let body_points builder (body : Mir.body) ~returns ~is_var ~(entry : int) ~ending =
  builder.body <- body;
  builder.returned <- returned_temporaries body;
  builder.aliases <- [];
  builder.binding <- [];
  let forks = Hashtbl.create 4 in
  let blocks = Array.length body.blocks in
  let firsts = Array.make blocks (-1) and lasts = Array.make blocks (-1) in
  let heads = Hashtbl.create 4 in
  let pending_edges = ref [] in
  let task_ends = Hashtbl.create 1 in
  Array.iteri
    (fun index (block : Mir.basic_block) ->
      builder.last <- (if index = 0 then Some entry else None);
      builder.block <- index;
      let first = builder.count in
      if index > 0 then emit_ builder (Bind []) block.terminator_origin;
      List.iter (statement builder forks ~is_var) block.statements;
      (* The other tasks of an early exit's group go on from the task's end,
         with the scopes around the task still open. The exit then ends those
         scopes once each task has ended, before it is taken. *)
      (match block.terminator with
      | Exit_tasks { tasks = { task_end = Some target; _ } :: _; _ } ->
          Hashtbl.replace task_ends index
            ((match builder.last with Some last -> last | None -> first), target)
      | _ -> ());
      (match block.terminator with
      | Exit_tasks { tasks; _ } ->
          List.iter
            (fun (left : Mir.left_task) -> List.iter (statement builder forks ~is_var) left.ends)
            tasks
      | _ -> ());
      let origin = block.terminator_origin in
      (match block.terminator with
      | Branch { condition; _ } -> evaluate builder condition
      | Switch_variant { place; _ } ->
          Option.iter (fun tracked -> emit_ builder (Read tracked) origin) (tracked builder place)
      | For { iteration; part; body = inside; after; loop } -> (
          let part_place = { Mir.root = Local part; projections = [] } in
          (match iteration with
          | Yielding called ->
              call builder called origin;
              hold builder part_place { (call_result builder called) with part = true }
          | Range { start; stop; _ } ->
              evaluate builder start;
              evaluate builder stop
          | Pull { cursor; _ } ->
              (* Each pull changes the cursor. *)
              Option.iter
                (fun tracked -> emit_ builder (Mutate tracked) origin)
                (tracked builder cursor);
              hold builder part_place { nothing with views = views_of_copy builder cursor });
          let head = emit builder (Bind []) origin in
          Hashtbl.replace heads index head;
          pending_edges := (head, `Block inside) :: (head, `Block after) :: !pending_edges;
          match loop.schedule with
          | Parallel_loop | Concurrent_loop ->
              builder.fork_join_loops <-
                {
                  keyword = (if loop.schedule = Parallel_loop then "parallel" else "concurrent");
                  body = { first = 0; limit = -inside };
                  bound = [];
                }
                :: builder.fork_join_loops
          | Sequential -> ())
      | Yield { mode; part; _ } ->
          (match part with
          | Use { place = { root = Local local; projections = [] }; _ }
            when (local_info builder local).kind = Temporary ->
              ()
          | _ -> evaluate builder part);
          let lent = lent_places builder part in
          if mode = Mut then begin
            List.iter
              (fun lent -> Option.iter (fun place -> emit_ builder (Mutate place) origin) lent)
              lent;
            let places =
              List.concat
                (List.mapi
                   (fun position lent ->
                     match lent with
                     | Some place -> [ { place; mode; at = origin; position } ]
                     | None -> [])
                   lent)
            in
            if List.length places > 1 then
              emit_ builder (Arguments { places; views = []; yielded = true }) origin
          end;
          let views =
            match operand_type part with
            | Some type_ when builder.is_view type_ -> views_of_operand builder part
            | _ -> []
          in
          emit_ builder (Yield_point { mode; lent; views }) origin
      | Return value | Exit_tasks { exit = Exit_return value; _ } ->
          (match value with
          | Some value -> (
              let is_returned =
                match value with Use { place; _ } -> not (is_temporary builder place) | _ -> false
              in
              evaluate builder ~returned:is_returned value;
              match operand_type value with
              | Some type_ when returns && builder.is_view type_ ->
                  emit_ builder (Return_view (views_of_operand builder value)) origin
              | _ -> ())
          | None -> ());
          ending origin
      | Goto _ | Exit_tasks _ | Iteration_end | Unreachable | Todo -> ());
      firsts.(index) <- (if index = 0 then entry else first);
      lasts.(index) <- (match builder.last with Some last -> last | None -> first))
    body.blocks;
  (* The innermost [For] whose body reaches each [Iteration_end]. *)
  let each_of = Hashtbl.create 4 in
  Array.iteri
    (fun index (block : Mir.basic_block) ->
      match block.terminator with
      | For { body = inside; after; _ } ->
          let visited = Hashtbl.create 8 in
          let rec visit block =
            if block <> after && not (Hashtbl.mem visited block) then begin
              Hashtbl.replace visited block ();
              match body.blocks.(block).terminator with
              | Iteration_end | Exit_tasks { exit = Exit_iteration; _ } ->
                  Hashtbl.replace each_of block index
              | For { after = inner_after; _ } -> visit inner_after
              | terminator -> List.iter visit (Mir.successors terminator)
            end
          in
          visit inside
      | _ -> ())
    body.blocks;
  Array.iteri
    (fun index (block : Mir.basic_block) ->
      let from = lasts.(index) in
      match block.terminator with
      | For _ -> ()
      | Iteration_end | Exit_tasks { exit = Exit_iteration; _ } -> (
          match Hashtbl.find_opt each_of index with
          | Some each -> link builder from (Hashtbl.find heads each)
          | None -> ())
      | Exit_tasks { exit = Exit_to target; _ } -> link builder from firsts.(target)
      | Exit_tasks _ -> ()
      | terminator ->
          List.iter (fun target -> link builder from firsts.(target)) (Mir.successors terminator))
    body.blocks;
  Hashtbl.iter (fun _ (before_exit, target) -> link builder before_exit firsts.(target)) task_ends;
  List.iter (fun (from, `Block target) -> link builder from firsts.(target)) !pending_edges;
  (* A parallel loop's body is the points of the blocks it runs. *)
  builder.fork_join_loops <-
    List.map
      (fun (loop : fork_join_loop) ->
        if loop.body.limit < 0 then (
          let inside = -loop.body.limit in
          let points = ref [] and visited = Hashtbl.create 8 in
          let rec visit block =
            if not (Hashtbl.mem visited block) then begin
              Hashtbl.replace visited block ();
              points := firsts.(block) :: lasts.(block) :: !points;
              match body.blocks.(block).terminator with
              | Iteration_end -> ()
              | For { after; _ } -> visit after
              | terminator -> List.iter visit (Mir.successors terminator)
            end
          in
          visit inside;
          let bound =
            List.concat_map
              (fun (statement : Mir.statement) ->
                match statement.kind with
                | Live locals -> List.filter_map (source builder) locals
                | _ -> [])
              body.blocks.(inside).statements
          in
          let first = List.fold_left min max_int !points in
          let first =
            match Hashtbl.find_opt builder.loop_entries inside with
            | Some entered -> max first entered
            | None -> first
          in
          { loop with body = { first; limit = List.fold_left max 0 !points + 1 }; bound })
        else loop)
      builder.fork_join_loops

(* The loans live at each point: a forward pass from the entries. *)
let live_loans builder =
  let count = builder.count in
  let live = Array.make count None in
  let pending = Queue.create () in
  List.iter
    (fun entry ->
      live.(entry) <- Some [];
      Queue.add entry pending)
    builder.entries;
  while not (Queue.is_empty pending) do
    let index = Queue.pop pending in
    let draft = Hashtbl.find builder.drafts index in
    let before = Option.value ~default:[] live.(index) in
    let after =
      let without = List.filter (fun (loan, _) -> not (List.mem loan draft.ends)) before in
      match draft.starts with
      | Some started -> if List.mem_assoc (fst started) without then without else started :: without
      | None -> without
    in
    List.iter
      (fun successor ->
        match live.(successor) with
        | None ->
            live.(successor) <- Some after;
            Queue.add successor pending
        | Some known ->
            let added = List.filter (fun loan -> not (List.mem loan known)) after in
            if added <> [] then begin
              live.(successor) <- Some (known @ added);
              Queue.add successor pending
            end)
      draft.draft_successors
  done;
  Array.map (fun loans -> List.concat_map snd (List.rev (Option.value ~default:[] loans))) live

(* The graph of a definition, or [None] if it has no code to run. *)
let of_mir ~plain ~is_view ~holds_function ~stores_function ~returns ~is_var (mir : Mir.t) : t =
  let builder =
    {
      drafts = Hashtbl.create 64;
      count = 0;
      entries = [];
      fork_join_blocks = [];
      fork_join_loops = [];
      plain;
      is_view;
      holds_function;
      stores_function;
      body = mir.body;
      captured = [];
      last = None;
      held = Hashtbl.create 32;
      returned = [];
      aliases = [];
      binding = [];
      storage_lend = false;
      block = 0;
      keeps_lent = [];
      loop_entries = Hashtbl.create 4;
    }
  in
  let entry = add builder Enter 0 in
  builder.entries <- [ entry ];
  let parameters (body : Mir.body) = List.filter_map (source builder) body.parameters in
  body_points builder mir.body ~returns ~is_var ~entry ~ending:(fun origin ->
      if returns then emit_ builder Exit origin);
  Array.iter
    (fun (lambda : Mir.body) ->
      builder.body <- lambda;
      let made_live =
        Array.to_list lambda.blocks
        |> List.concat_map (fun (block : Mir.basic_block) ->
            List.concat_map
              (fun (statement : Mir.statement) ->
                match statement.kind with Live locals -> locals | _ -> [])
              block.statements)
      in
      builder.captured <-
        List.filter_map
          (fun local ->
            match lambda.locals.(local).kind with
            | Source { local = core; _ }
              when (not (List.mem local lambda.parameters)) && not (List.mem local made_live) ->
                Some core
            | _ -> None)
          (List.init (Array.length lambda.locals) Fun.id);
      Hashtbl.reset builder.held;
      let entry = add builder Enter 0 in
      builder.entries <- builder.entries @ [ entry ];
      builder.last <- Some entry;
      let bound = parameters lambda in
      let entry = emit builder (Bind bound) 0 in
      body_points builder lambda ~returns:false ~is_var ~entry ~ending:(fun origin ->
          emit_ builder (Scope_end bound) origin))
    mir.lambdas;
  let loans = live_loans builder in
  {
    points =
      Array.init builder.count (fun index ->
          let draft = Hashtbl.find builder.drafts index in
          {
            action = draft.draft_action;
            origin = draft.draft_origin;
            loans = loans.(index);
            successors = draft.draft_successors;
          });
    entries = builder.entries;
    fork_join_blocks = List.rev builder.fork_join_blocks;
    fork_join_loops = List.rev builder.fork_join_loops;
  }
