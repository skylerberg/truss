(* Loans and views, checked on the MIR of a definition's bodies: the
   definition's own and each lambda's, which runs when the lambda is called,
   not where it is made. The check prevents dangling views, mutation of a
   borrowed place, moves the place's root forbids, and data races.

   Each statement and terminator is read once, in block order, into the
   actions the checks follow: its reads, which the move analysis gives in
   evaluation order, its mutations, and the views it binds and stores. A
   forward analysis over the actions gives, before each action, the views
   each holder may store and the loans that are open. A place is in use
   where an open loan borrows it, or where a live holder stores a view of
   it. A view dangles where the MIR drops the local or the temporary that
   it views while a live holder stores it. Specifications and [proof]
   blocks have no actions, because they do not run. *)
open Context

(* A loan: a borrow of a place that lasts for a region of code, as the MIR's
   [Loan_start] and [Loan_end] mark it. While a read-only loan is open, the
   place cannot be mutated. While a [mut] loan is open, the place cannot be
   used at all. *)
type loan = { borrowed : Place.t; mode : Types.mode; duration : Mir.loan_duration }

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
  | Read of Place.t  (** The place is read or borrowed read-only. *)
  | Move of {
      place : Place.t;
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
  | Yield_point of { mode : Types.mode; lent : Place.t option list; views : view list }
      (** Where a lending method lends its part. [lent] is the places that the part lends, where
          [None] is a place that the check does not track. [views] is the views of the part, if it
          has a view type. *)
  | Bind_views of { locals : Core.local list; views : view list }
      (** A pattern binds [locals] to a value that has these views. *)
  | Store of { place : Place.t; views : view list; overwrites : bool }
      (** A value that has these views is stored in the place: by an assignment, or by a call that
          borrows the place [mut] and may store one of its view arguments there. If [overwrites],
          the value replaces the whole value of the place's root, whose views end. *)
  | Return_view of view list  (** The function returns a value that has these views. *)
  | Drop of (Place.root * Core.origin) list
      (** The MIR ends these owners of values: each with where it is made, a temporary's expression
          or a local's binding. A view of one of them dangles from here. *)
  | Bind_lent_part of Types.ty
      (** A [let] binds a part that a lending call lent. The loan ends with the statement. *)
  | Pass_owned_function of view list
      (** A function value that has these views is passed to an [own] parameter. The callee may
          store the function, so the function could outlive its captures. *)
  | Start_loan of { loan : int; loans : loan list }  (** A loan starts, lending these places. *)
  | End_loans of int list
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
          the places are those that a constructor lends where a lending method lends it, and [views]
          is empty. *)

(* A position in a block: one of its statements, then its terminator. *)
type position = { block : Mir.block; index : int }
type step = { action : action; origin : Core.origin }

(* The builder *)

(* What the builder knows of a local of the MIR. *)
type held = {
  place : Place.t option;  (** The tracked place it is, for a lent part or an alias. *)
  views : view list;  (** The views of the value it holds, for a temporary. *)
  slice : Place.t option;  (** For a slice, the elements it views. *)
  lent : Place.t option list;  (** For a constructed value, the places its fields lend. *)
  collection : (Place.t option * Types.ty) option;
      (** For an element of a collection, the collection and its type. *)
  fresh : bool;
      (** For a temporary, whether its value is a new one, which is dropped where the temporary is
          [Dead]: not a string literal, a lambda, a value read out of a named place, or a part that
          a loop's callee lends. *)
  alias : Mir.place option;
  part : bool;  (** Whether it is the element that a loop over a collection is lent. *)
}

let nothing =
  {
    place = None;
    views = [];
    slice = None;
    lent = [];
    collection = None;
    fresh = true;
    alias = None;
    part = false;
  }

type builder = {
  context : Context.context;
  mutable moves : Moves.t;  (** The move analysis of the body being written *)
  mutable body : Mir.body;
  mutable captured : Core.local list;
  held : (Mir.local, held) Hashtbl.t;
  mutable returned : Mir.local list;  (** The temporaries whose value the body returns. *)
  mutable aliases : Mir.local list;
  mutable binding : Mir.local list;  (** The locals made live and not yet given a value. *)
  mutable storage_lend : bool;
      (** Whether the last lend was of an element of a collection, which lends nothing for the
          statement. *)
  mutable keeps_lent : (Mir.local * Mir.local * Types.ty * Core.origin) list;
      (** Each binding of a lent part not yet dead: the binding, the part, its type, and where it is
          bound. A binding still live where its part ends would outlive the loan. *)
  loop_entries : (Mir.block, int) Hashtbl.t;
      (** For the first block of a loop's body, the first position after the loop's loan starts. *)
  mutable loop_elements : Mir.local list;
      (** The [Lent] locals of the elements that the body's loops over collections lend to their
          iterations. *)
  mutable position : position;  (** The position being written *)
  mutable written : step list;  (** Its actions so far, most recent first *)
}

let emit_ builder action origin = builder.written <- { action; origin } :: builder.written
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
   type is copied, not borrowed. A temporary that owns a new value is a
   place of its own, which the MIR drops where the temporary is [Dead]. *)
let views_of_borrow builder (place : Mir.place) type_ =
  match tracked builder place with
  | Some place -> [ { place; copied_out = plain builder.context type_ } ]
  | None -> (
      match (place.root, temporary_of builder place) with
      | Local _, Some temporary
        when (held builder temporary).fresh
             && (not (plain builder.context type_))
             && not (is_view builder.context type_) ->
          [ { place = { root = Temporary temporary; steps = [] }; copied_out = false } ]
      | Local local, _ -> (held builder local).views
      | Constant _, _ -> [])

let operand_type : Mir.operand -> Types.ty option = function
  | Use { type_; _ } | Borrow { type_; _ } | Take { type_; _ } -> Some type_
  | Constant _ -> None

let views_of_operand builder (operand : Mir.operand) =
  match operand with
  | Use { place; _ } | Take { place; _ } -> views_of_copy builder place
  | Borrow { place; type_; _ } -> views_of_borrow builder place type_
  | Constant _ -> []

(* The views of an argument. A value passed to a read-only or [mut]
   parameter is borrowed for the call, as a place is. *)
let views_of_argument builder (mode : Types.mode) (operand : Mir.operand) =
  match operand with
  | Use { place; type_; _ } when mode <> Own -> views_of_borrow builder place type_
  | _ -> views_of_operand builder operand

(* The views of a part of a value, if it has a view type. *)
let views_of_part builder (operand : Mir.operand) =
  match operand_type operand with
  | Some type_ when is_view builder.context type_ -> views_of_operand builder operand
  | _ -> []

(* The places an operand depends on until its operation runs: the place it
   borrows, or the places its value views. *)
let operand_borrows builder (operand : Mir.operand) =
  match operand with
  | Borrow { place; _ } -> Option.to_list (tracked builder place)
  | Use { type_; _ } when is_view builder.context type_ ->
      List.map (fun (view : view) -> view.place) (views_of_operand builder operand)
  | Use _ | Take _ | Constant _ -> []

(* Whether a call's result may be a view of an argument: the argument is
   borrowed and is not [Plain], or it is itself a view. *)
let result_may_view builder (mode : Types.mode) type_ =
  (mode <> Own && not (plain builder.context type_)) || is_view builder.context type_

(* The arguments that a call's result may view, each with its parameter's
   mode. *)
let viewable_arguments builder (call : Mir.call) =
  List.filter_map
    (fun (argument : Mir.argument) ->
      match argument with
      | Passed { mode; value; _ } -> (
          match operand_type value with
          | Some type_ when result_may_view builder mode type_ -> Some (mode, value)
          | _ -> None)
      | Default -> None)
    call.arguments

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
  | Temporary _ | Constant _ | Environment -> false

(* A read of a place: a copy, or a move out of it, as the move analysis
   says. A read-only borrow reads the place, and a [mut] borrow starts where
   its operation runs. A compound assignment's old value is only read: the
   statement assigns the target again before any other code runs. *)
let evaluate builder ~returned (use : Moves.use) =
  let read place origin =
    Option.iter (fun tracked -> emit_ builder (Read tracked) origin) (tracked builder place)
  in
  match use.operand with
  | Some (Use { place; type_; origin; _ } | Borrow { place; type_; origin; _ }) when use.moves -> (
      match tracked builder place with
      | Some tracked ->
          emit_ builder
            (Move { place = tracked; type_; returned; captured = is_captured builder tracked })
            origin
      | None -> if is_lent_part builder place then emit_ builder (Move_out_of_lent type_) origin)
  | Some (Use { place; origin; _ } | Take { place; origin; _ }) -> read place origin
  | Some (Borrow { place; mode = Read | Own; origin; _ }) -> (
      match place.root with
      | Local local when List.mem local builder.aliases -> ()
      | _ -> read place origin)
  | None -> read use.place use.origin
  | Some (Borrow { mode = Mut; _ } | Constant _) -> ()

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

(* A call, once its reads are written: its [mut] borrows, the aliasing of
   what it borrows, the views it may store in a [mut] argument, and the
   functions it may keep. *)
let call builder (call : Mir.call) origin =
  List.iter
    (function
      | Mir.Passed { mode = Mut; value; _ } -> borrow_mut builder value | Passed _ | Default -> ())
    call.arguments;
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
                 when is_view builder.context type_ ->
                   [ (position, views_of_operand builder value, origin) ]
               | Passed _ | Default -> [])
             call.arguments)
  in
  if List.length places > 1 || (places <> [] && views <> []) then
    emit_ builder (Arguments { places; views; yielded = false }) origin;
  let can_store_in target (other : Mir.operand) =
    match operand_type other with
    | Some (Types.Function { output = Returns output; _ }) when not (is_view builder.context output)
      ->
        holds_function builder.context target
    | _ -> true
  in
  List.iter
    (fun (argument : Mir.argument) ->
      match argument with
      | Passed { mode = Mut; value = Borrow { place; type_; _ } as target; _ }
        when is_view builder.context type_ -> (
          match tracked builder place with
          | Some place ->
              let others =
                List.filter
                  (fun other ->
                    other != target
                    && (match operand_type other with
                      | Some type_ -> is_view builder.context type_
                      | None -> false)
                    && can_store_in type_ other)
                  (List.map snd (viewable_arguments builder call))
              in
              emit_ builder
                (Store
                   {
                     place;
                     views = List.concat_map (views_of_operand builder) others;
                     overwrites = false;
                   })
                origin
          | None -> ())
      | _ -> ())
    call.arguments;
  List.iteri
    (fun position (argument : Mir.argument) ->
      match argument with
      | Passed { mode = Own; value = Use { type_ = Types.Function _; origin; _ } as value; _ }
        when stores_function builder.context call.callee position ->
          emit_ builder (Pass_owned_function (views_of_operand builder value)) origin
      | _ -> ())
    call.arguments

(* What a call's result holds: views of the arguments it may view. *)
let call_result builder (call : Mir.call) =
  {
    nothing with
    views =
      List.concat_map
        (fun (mode, value) -> views_of_argument builder mode value)
        (viewable_arguments builder call);
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

(* What an rvalue's value holds. *)
let rvalue builder (value : Mir.rvalue) : held =
  match value with
  | Operand operand ->
      let views = views_of_operand builder operand in
      let lent = lent_places builder operand in
      let slice, fresh =
        match operand with
        | Use { place = { root = Local local; _ } as place; _ } when is_temporary builder place ->
            ((held builder local).slice, (held builder local).fresh)
        | Use _ | Take _ | Borrow _ -> (None, false)
        | Constant _ -> (None, false)
      in
      { nothing with views; lent = (match operand with Borrow _ -> [] | _ -> lent); slice; fresh }
  | Operation _ | Compare _ -> nothing
  | Not operand | Convert { value = operand; _ } | To_any { value = operand; _ } | Copy operand ->
      { nothing with views = views_of_operand builder operand }
  | Construct { fields; _ } ->
      let given = List.filter_map snd fields in
      {
        nothing with
        views = List.concat_map (views_of_part builder) given;
        lent = List.concat_map (lent_places builder) given;
      }
  | Array elements -> { nothing with views = List.concat_map (views_of_part builder) elements }
  | Is_variant _ -> nothing
  | Lambda { captures; _ } -> (
      match captures with
      | [] -> { nothing with fresh = false }
      | _ ->
          {
            nothing with
            fresh = false;
            views =
              { place = { root = Environment; steps = [] }; copied_out = false }
              :: List.map
                   (fun (capture : Mir.capture) ->
                     { place = { root = Local capture.local; steps = [] }; copied_out = false })
                   captures;
          })
  | Function_value _ | Value_parameter _ -> nothing

(* A local the body is about to bind: its first assignment is its value. *)
let bound_value builder (local : Mir.local) (core : Core.local) (value : Mir.rvalue) origin ~is_var
    =
  let type_ = (local_info builder local).type_ in
  let holds_views = is_view builder.context type_ in
  let result = rvalue builder value in
  let is_loop_part (place : Mir.place) =
    match place.root with Local part -> (held builder part).part | Constant _ -> false
  in
  (match value with
  | Operand
      (Borrow { place = { root = Local part; _ } as place; type_ = part_type; origin = at; _ })
    when (not is_var) && is_lent_part builder place
         && (not (is_loop_part place))
         && ((not (plain builder.context part_type)) || is_view builder.context part_type) ->
      builder.keeps_lent <- (local, part, part_type, at) :: builder.keeps_lent
  | _ -> ());
  let views =
    match value with
    | Operand (Borrow { place; type_ = part_type; _ })
      when holds_views || is_temporary builder place || is_loop_part place
           || (Option.is_some (tracked builder place) && not (plain builder.context part_type)) ->
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
    if from_part && plain builder.context type_ then
      List.map (fun (view : view) -> { view with copied_out = true }) views
    else views
  in
  if holds_views || views <> [] then emit_ builder (Bind_views { locals = [ core ]; views }) origin

let returned_temporaries (body : Mir.body) =
  let returned = ref [] in
  Array.iter
    (fun (block : Mir.basic_block) ->
      match block.terminator with
      | Return (Some (Use { place = { root = Local local; projections = [] }; _ }))
      | Cancel
          { returned = Some (Use { place = { root = Local local; projections = [] }; _ }, _); _ }
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
let loans_of builder (borrowed : Mir.operand) mode duration : loan list =
  List.map (fun borrowed : loan -> { borrowed; mode; duration }) (operand_borrows builder borrowed)

(* Writes the reads of a statement or a terminator, in evaluation order, as
   the move analysis gives them: each operand evaluated. [skip] leaves out
   the reads that the code around writes another way. *)
let read_uses builder ?(returned = fun _ -> false) ?(skip = fun _ -> false) uses =
  List.iter
    (fun (use : Moves.use) -> if not (skip use) then evaluate builder ~returned:(returned use) use)
    uses

let statement builder (statement : Mir.statement) =
  let origin = statement.origin in
  let uses = Moves.statement_uses builder.moves statement in
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
      (* A local bound [own] and a temporary own their values, which end
         here. A local bound to a place, and a lent part, own nothing. *)
      let dropped =
        List.filter_map
          (fun local ->
            let info = local_info builder local in
            match info.kind with
            | Temporary -> Some (Place.Temporary local, info.origin)
            | Source { local = core; mode = Own; _ } -> Some (Place.Local core, info.origin)
            | Source _ | Lent _ -> None)
          locals
      in
      if dropped <> [] then emit_ builder (Drop dropped) origin;
      builder.keeps_lent <-
        List.filter
          (fun (binding, part, _, _) -> not (List.mem binding locals || List.mem part locals))
          builder.keeps_lent
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
          | Operand (Use { place; _ })
            when List.mem local builder.returned && Option.is_some (tracked builder place) ->
              read_uses builder ~returned:(fun _ -> true) uses;
              hold builder target { nothing with views = views_of_copy builder place }
          | _ ->
              read_uses builder uses;
              hold builder target (rvalue builder value))
      | Lent _ -> (
          read_uses builder uses;
          builder.aliases <- local :: builder.aliases;
          let result = rvalue builder value in
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
          read_uses builder uses;
          bound_value builder local core value origin
            ~is_var:(List.mem core builder.context.mutable_locals))
  | Assign { target; value; _ } -> (
      read_uses builder uses;
      let result = rvalue builder value in
      match tracked builder target with
      | Some place -> (
          let type_ = match value with Operand operand -> operand_type operand | _ -> None in
          writes_through builder ~whole:false target (Option.value ~default:Types.unit type_) origin;
          emit_ builder (Assign place) origin;
          match type_ with
          | Some type_ when is_view builder.context type_ ->
              emit_ builder
                (Store { place; views = result.views; overwrites = place.steps = [] })
                origin
          | _ -> ())
      | None -> hold builder { target with projections = [] } result)
  | Call { destination; call = called } ->
      read_uses builder uses;
      call builder called origin;
      Option.iter
        (fun destination -> hold builder destination (call_result builder called))
        destination
  | Template { destination; call = called; _ } ->
      read_uses builder uses;
      call builder called origin;
      hold builder destination (call_result builder called)
  | Lend { part; call = called } -> (
      let is_storage type_ =
        Types.is_well_known List type_ || Types.is_well_known Slice type_
        || Types.is_builtin Array type_
      in
      let is_loop_element = List.mem part builder.loop_elements in
      let element_of collection collection_type =
        let collection_place = tracked builder collection in
        Some
          ( Option.map
              (fun (place : Place.t) ->
                { place with steps = place.steps @ [ Element { node = called.node; origin } ] })
              collection_place,
            (collection_place, collection_type) )
      in
      let element =
        match (called.callee, called.arguments) with
        | ( Trait_method { trait; name = "at"; self_type; _ },
            Passed { value = Borrow { place = collection; type_ = collection_type; _ }; _ } :: _ )
          when (Well_known.is Index trait.trait || Well_known.is Index_mut trait.trait)
               && is_storage self_type ->
            element_of collection collection_type
        (* A loop over a [List], a [Slice], or an [Array] lends each iteration
           the element at its position, as an index does. *)
        | ( ( Trait_method { name = "element"; _ }
            | Function { path = Method { name = "element"; _ }; _ } ),
            Passed { value = Borrow { place = collection; type_ = collection_type; _ }; _ } :: _ )
          when is_loop_element && is_storage collection_type ->
            element_of collection collection_type
        | _ -> None
      in
      match element with
      | Some (place, collection) ->
          (* An element of a [List], a [Slice], or an [Array] is a place of
             its own: the index reads the collection, and lends no part of
             it for the statement. *)
          read_uses builder (List.tl uses);
          builder.storage_lend <- true;
          hold builder
            { Mir.root = Local part; projections = [] }
            { nothing with place; collection = Some collection }
      | None ->
          read_uses builder uses;
          call builder called origin;
          (* The element that a loop lends an iteration views what the
             collection does. *)
          hold builder
            { Mir.root = Local part; projections = [] }
            { (call_result builder called) with part = is_loop_element })
  | Slice { destination; base; call = called } ->
      (* The slice's base is the call's first argument, which reads it. *)
      read_uses builder ~skip:(fun use -> use.operand = None) uses;
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
      hold builder destination { nothing with views; slice = elements }
  | Assert _ | Echo _ -> read_uses builder uses
  | Provide { provided; _ } ->
      read_uses builder uses;
      List.iter
        (fun (provided : Mir.provided) ->
          if provided.mode = Mut then borrow_mut builder provided.value)
        provided
  | Loan_start { loan; borrowed; mode; duration } ->
      let loans =
        if duration = Rest_of_statement && builder.storage_lend then []
        else loans_of builder borrowed mode duration
      in
      builder.storage_lend <- false;
      emit_ builder (Start_loan { loan; loans }) origin;
      if duration = Loop_body then
        Hashtbl.replace builder.loop_entries builder.position.block (builder.position.index + 1)
  | Loan_end loans -> emit_ builder (End_loans loans) origin
  | Provide_end | Ghost_assert _ | Matched _ | Proof _ -> ()

(* A pull of a cursor calls its [next], which may change the cursor. A pull
   happens before the first iteration and at the end of each, whether or
   not another follows, so a view of the cursor kept from one iteration is
   in use where the pull after it changes the cursor. *)
let pull builder (iteration : Mir.iteration) origin =
  match iteration with
  | Pull { cursor; _ } ->
      Option.iter (fun tracked -> emit_ builder (Mutate tracked) origin) (tracked builder cursor)
  | Range _ -> ()

let terminator builder ~returns (basic : Mir.basic_block) =
  let origin = basic.terminator_origin in
  let uses = Moves.terminator_uses builder.moves basic in
  let returning value =
    read_uses builder
      ~returned:(fun (use : Moves.use) ->
        match use.operand with
        | Some (Use { place; _ }) -> not (is_temporary builder place)
        | _ -> false)
      uses;
    match value with
    | Some value -> (
        match operand_type value with
        | Some type_ when returns && is_view builder.context type_ ->
            emit_ builder (Return_view (views_of_operand builder value)) origin
        | _ -> ())
    | None -> ()
  in
  match basic.terminator with
  | Branch _ | Switch_variant _ -> read_uses builder uses
  | For { iteration; part; _ } -> (
      let part_place = { Mir.root = Local part; projections = [] } in
      match iteration with
      | Range _ -> read_uses builder uses
      | Pull { cursor; _ } ->
          pull builder iteration origin;
          (* The [next] of a cursor returns each value owned. *)
          hold builder part_place
            { nothing with views = views_of_copy builder cursor; fresh = true })
  | Yield { mode; part; _ } ->
      (* A constructor built where it is yielded lends each place among its
         leaves, and its other leaves are values. A temporary yielded is
         read where it is made. *)
      let rec leaves : Mir.yielded -> Mir.operand list = function
        | Part operand -> [ operand ]
        | Built { fields; _ } ->
            List.concat_map (fun (_, field) -> Option.fold ~none:[] ~some:leaves field) fields
      in
      read_uses builder
        ~skip:(fun (use : Moves.use) ->
          match (part, use.operand) with
          | Part (Use { place = { root = Local local; projections = [] }; _ }), _ ->
              (local_info builder local).kind = Temporary
          | Built _, Some (Borrow _) -> true
          | _ -> false)
        uses;
      let lent = List.concat_map (lent_places builder) (leaves part) in
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
        match part with
        | Part operand -> (
            match operand_type operand with
            | Some type_ when is_view builder.context type_ -> views_of_operand builder operand
            | _ -> [])
        | Built { type_; _ } when is_view builder.context type_ ->
            List.concat_map
              (fun (leaf : Mir.operand) ->
                match leaf with
                | Borrow { place; type_; _ } -> views_of_borrow builder place type_
                | _ -> views_of_part builder leaf)
              (leaves part)
        | Built _ -> []
      in
      emit_ builder (Yield_point { mode; lent; views }) origin
  (* An early exit that returns a value hands it to the code after its
     group, which returns it. *)
  | Return value -> returning value
  | Cancel { returned; _ } -> returning (Option.map fst returned)
  | Iteration_end { loop } -> (
      match builder.body.blocks.(loop).terminator with
      | For { iteration; _ } -> pull builder iteration origin
      | _ -> ())
  | Join _ | Goto _ | Fork _ | Resume _ | Unreachable | Written_unreachable | Todo -> ()

(* The fork-joins of a body: a [parallel] or [concurrent] block, whose
   branches may run at the same time, and a [parallel for] or [concurrent
   for], whose iterations may. [keyword] names it in messages. A loop's
   [bound] is the locals its pattern binds. *)
type fork_join_block = { keyword : string; branches : position list list }

type fork_join_loop = {
  keyword : string;
  body : position list;
  bound : Core.local list;
  temporaries : Mir.local list;  (** The temporaries that the body makes. *)
}

type actions = {
  body : Mir.body;
  steps : step list array array;  (** Each position's actions, in order *)
  fork_join_blocks : fork_join_block list;
  fork_join_loops : fork_join_loop list;
}

(* The actions of a body. *)
let of_body (builder : builder) (body : Mir.body) ~returns : actions =
  builder.body <- body;
  builder.returned <- returned_temporaries body;
  builder.aliases <- [];
  builder.binding <- [];
  Hashtbl.reset builder.loop_entries;
  builder.loop_elements <-
    Array.to_list body.blocks
    |> List.filter_map (fun (basic : Mir.basic_block) ->
        match basic.terminator with
        | For { lent = Some { element; _ }; _ } -> Some element
        | _ -> None);
  let shape =
    Array.map (fun (basic : Mir.basic_block) -> List.length basic.statements + 1) body.blocks
  in
  let steps = Array.map (fun count -> Array.make count []) shape in
  let write position body =
    builder.position <- position;
    body ();
    steps.(position.block).(position.index) <- List.rev builder.written;
    builder.written <- []
  in
  Array.iteri
    (fun block (basic : Mir.basic_block) ->
      List.iteri
        (fun index statement' -> write { block; index } (fun () -> statement builder statement'))
        basic.statements;
      write
        { block; index = List.length basic.statements }
        (fun () -> terminator builder ~returns basic))
    body.blocks;
  let positions_of ?(from = fun _ -> None) blocks =
    List.concat_map
      (fun block ->
        let first = Option.value ~default:0 (from block) in
        List.init (max 0 (shape.(block) - first)) (fun offset -> { block; index = first + offset }))
      (List.sort_uniq compare blocks)
  in
  let fork_join_blocks =
    Array.to_list body.blocks
    |> List.filter_map (fun (basic : Mir.basic_block) ->
        match basic.terminator with
        | Fork { concurrent; branches; _ } ->
            Some
              {
                keyword = (if concurrent then "concurrent" else "parallel");
                branches =
                  List.map (fun (branch : Mir.branch) -> positions_of branch.blocks) branches;
              }
        | _ -> None)
  in
  (* A parallel loop's body is the positions of the blocks it runs, from
     where the loop's loan starts, and not the pull at the end of each
     iteration, which the loop runs between iterations. *)
  let fork_join_loops =
    Array.to_list (Array.mapi (fun block basic -> (block, basic)) body.blocks)
    |> List.filter_map (fun (loop_block, (basic : Mir.basic_block)) ->
        match basic.terminator with
        | For
            {
              body = inside;
              blocks;
              loop = { schedule = Parallel_loop | Concurrent_loop; _ } as loop;
              _;
            } ->
            Some
              {
                keyword = (if loop.schedule = Parallel_loop then "parallel" else "concurrent");
                body =
                  List.filter
                    (fun { block; index } ->
                      index < shape.(block) - 1
                      || Mir.iteration_loop body.blocks.(block).terminator <> Some loop_block)
                    (positions_of
                       ~from:(fun block ->
                         if block = inside then Hashtbl.find_opt builder.loop_entries inside
                         else None)
                       blocks);
                bound =
                  List.concat_map
                    (fun (statement : Mir.statement) ->
                      match statement.kind with
                      | Live locals -> List.filter_map (source builder) locals
                      | _ -> [])
                    body.blocks.(inside).statements;
                temporaries =
                  List.concat_map
                    (fun block ->
                      List.concat_map
                        (fun statement ->
                          List.filter_map
                            (fun (path : Moves.path) ->
                              if (local_info builder path.local).kind = Temporary then
                                Some path.local
                              else None)
                            (Moves.given_by statement))
                        body.blocks.(block).statements)
                    blocks;
              }
        | _ -> None)
  in
  { body; steps; fork_join_blocks; fork_join_loops }

(* Views *)

(* The views that each holder may store. A holder with an entry stores a
   value of a view type, even if the entry is empty. *)
type held_views = (Place.root * view list) list

let views_held_by (held_views : held_views) (holder : Place.root) = List.assoc_opt holder held_views

let add_views (held_views : held_views) holder views : held_views =
  let known = Option.value ~default:[] (views_held_by held_views holder) in
  let added = List.filter (fun view -> not (List.mem view known)) views in
  (holder, known @ added) :: List.remove_assoc holder held_views

(* Whether a local is an alias of another place: a [let] bound to a place, a
   pattern binding of a part of a place, or a loop variable bound to an
   element. A parameter is not an alias: the function does not know its
   argument. *)
let aliases_place context (root : Place.root) =
  match root with
  | Local local ->
      local <> Self && (not (List.mem local context.parameters)) && kind context root <> Owned
  | Temporary _ | Constant _ | Environment -> false

(* Expands views through the holders that they name, so that the result
   names the places that own the borrowed data.

   - A view that borrows a place: the place itself, and the views that the
     place's root stores.
   - A copy of a view stored in a place ([copied_out]): only the views that
     the place's root stores.
   - A view of an alias: the views of the alias. After [match self.user {
     Some(found) => ... }], a slice of [found] views [self.user].

   If the root has no entry, as for a parameter, the view is kept as it is.
   The place then represents whatever the stored view borrows. *)
let resolve context (held_views : held_views) (views : view list) : view list =
  List.concat_map
    (fun (view : view) ->
      match views_held_by held_views view.place.root with
      | Some known when view.copied_out || aliases_place context view.place.root -> known
      | Some known -> known @ [ view ]
      | None -> [ view ])
    views

(* Whether the viewed place is dropped when the function returns, so that a
   view of it would dangle in the caller: a local, a temporary, a lambda's
   environment record, or an [own] parameter. A copy of a view that an
   [own] parameter stores is not: it borrows the caller's data, which
   outlives the function. *)
let lifetime_ends_at_return context (view : view) =
  match view.place.root with
  | Constant _ -> false
  | Temporary _ | Environment -> true
  | Local local ->
      if local = Self || List.mem local context.parameters then
        kind context view.place.root = Owned && not view.copied_out
      else true

(* Whether the place outlives the function: a [mut] parameter, or [self] in
   a [mut self] method. The caller still owns it after the call. *)
let outlives_function context (place : Place.t) =
  kind context place.root = Borrowed_mut
  &&
  match place.root with
  | Local local -> List.mem local context.parameters
  | Temporary _ | Constant _ | Environment -> false

(* The analysis *)

(* What holds before an action: the views each holder may store, and the
   open loans, newest first. *)
type state = { views : held_views; loans : (int * loan list) list }

let transfer context (step : step) (before : state) : state =
  match step.action with
  | Bind locals ->
      {
        before with
        views =
          List.filter
            (fun (holder, _) -> not (List.exists (fun local -> holder = Place.Local local) locals))
            before.views;
      }
  | Bind_views { locals; views } ->
      let viewed = resolve context before.views views in
      {
        before with
        views =
          List.fold_left
            (fun held_views holder ->
              (Place.Local holder, viewed) :: List.remove_assoc (Place.Local holder) held_views)
            before.views locals;
      }
  | Store { place; views; overwrites } -> (
      let viewed = resolve context before.views views in
      if overwrites then
        { before with views = (place.root, viewed) :: List.remove_assoc place.root before.views }
      else
        match viewed with
        | [] -> before
        | viewed -> { before with views = add_views before.views place.root viewed })
  | Start_loan { loan; loans } ->
      if List.mem_assoc loan before.loans then before
      else { before with loans = (loan, loans) :: before.loans }
  | End_loans ended ->
      { before with loans = List.filter (fun (loan, _) -> not (List.mem loan ended)) before.loans }
  | Read _ | Move _ | Move_out_of_lent _ | Mutate _ | Assign _ | Yield_point _ | Return_view _
  | Drop _ | Bind_lent_part _ | Pass_owned_function _ | Write_through _ | Arguments _ ->
      before

(* Merges a state into a known one: the merged state, where it grew. *)
let join (after : state) ~(into : state) =
  let views =
    List.filter
      (fun (holder, places) ->
        match views_held_by into.views holder with
        | Some known -> List.exists (fun place -> not (List.mem place known)) places
        | None -> true)
      after.views
  and loans = List.filter (fun loan -> not (List.mem loan into.loans)) after.loans in
  if views = [] && loans = [] then None
  else
    Some
      {
        views =
          List.fold_left
            (fun held_views (holder, places) -> add_views held_views holder places)
            into.views views;
        loans = into.loans @ loans;
      }

(* The state before each action of each position that some path reaches. *)
let forward context (actions : actions) =
  let blocks = Array.length actions.steps in
  let entries = Array.make blocks None and pending = Queue.create () in
  if blocks > 0 then begin
    entries.(0) <- Some { views = []; loans = [] };
    Queue.add 0 pending
  end;
  let through steps state =
    List.fold_left (fun state step -> transfer context step state) state steps
  in
  while not (Queue.is_empty pending) do
    let block = Queue.pop pending in
    let after =
      Array.fold_left
        (fun state steps -> through steps state)
        (Option.get entries.(block))
        actions.steps.(block)
    in
    List.iter
      (fun successor ->
        match entries.(successor) with
        | None ->
            entries.(successor) <- Some after;
            Queue.add successor pending
        | Some known -> (
            match join after ~into:known with
            | Some merged ->
                entries.(successor) <- Some merged;
                Queue.add successor pending
            | None -> ()))
      (Mir.block_successors actions.body block)
  done;
  Array.mapi
    (fun block entry ->
      Option.map
        (fun entry ->
          let state = ref entry in
          Array.map
            (fun steps ->
              Array.of_list
                (List.map
                   (fun step ->
                     let before = !state in
                     state := transfer context step before;
                     before)
                   steps))
            actions.steps.(block))
        entry)
    entries

let overlaps left right = Place.overlap left right <> Disjoint

(* What holds before an action. *)
type here = {
  views : held_views;  (** The views each holder may store *)
  loans : loan list;  (** The open loans, newest first *)
  is_live : Core.local -> bool;  (** Whether a local is live after the action *)
  origin : Core.origin;  (** Where the action is *)
}

(* The message for a use of a place that a loan covers. [viewed] is true if
   the loan covers the place only because the borrowed place stores a view
   of it. *)
let loan_message context (loan : loan) ~viewed (place : Place.t) ~verb =
  let lender =
    match loan.duration with
    | Loop_body -> "the loop"
    | Provide_body -> "the `provide` block"
    | Rest_of_statement -> "a lending call, until this statement ends,"
    | Operand_evaluation -> "an earlier operand of this expression"
  and through =
    if viewed then Printf.sprintf " through `%s`, which views it" (show context loan.borrowed)
    else ""
  in
  match loan.mode with
  | Mut ->
      Printf.sprintf "`%s` is borrowed `mut` by %s%s, so it cannot be used here."
        (show context place) lender through
  | Read | Own ->
      Printf.sprintf "`%s` cannot %s while %s borrows it%s." (show context place) verb lender
        through

(* Reports a view that would dangle once the function returns: one of a
   lambda's captured variables, or of a place the function drops. [doing]
   says what the code does with the value, and [fix] what to do instead.
   Says whether it reported one. *)
let dangles context at ~views ~doing ~fix =
  let report_view = report context View_escapes at in
  match List.find_opt (lifetime_ends_at_return context) views with
  | Some { place = { root = Environment; _ }; _ } ->
      report_view
        (Printf.sprintf
           "This %s a capturing lambda. A lambda's captured variables live in this function's \
            stack frame, so the lambda would dangle. %s"
           doing fix);
      true
  | Some { place = { root = Temporary _; _ }; _ } ->
      report_view
        (Printf.sprintf
           "This %s a view of a temporary, which is dropped before the function returns, so the \
            view would dangle. %s"
           doing fix);
      true
  | Some view ->
      report_view
        (Printf.sprintf
           "This %s a view of `%s`, which is dropped when the function returns, so the view would \
            dangle. %s"
           doing
           (show_root context view.place.root)
           fix);
      true
  | None -> false

(* Records, in [context.must_be_disjoint], two parts of one collection that
   must be disjoint, and says whether two places surely overlap. *)
let surely_overlap context first second =
  match Place.overlap first second with
  | Overlapping -> true
  | Maybe_disjoint (first, second) ->
      context.must_be_disjoint <- (first, second) :: context.must_be_disjoint;
      false
  | Disjoint -> false

(* Reports the errors of one body's loans and views. *)
let check_body context (actions : actions) moves =
  let states = forward context actions in
  let live = Moves.live moves actions.body ~drops:false in
  let mir_local = Hashtbl.create 16 in
  Array.iteri
    (fun local (info : Mir.local_info) ->
      match info.kind with
      | Source { local = core; _ } -> Hashtbl.replace mir_local core local
      | Temporary | Lent _ -> ())
    actions.body.locals;
  (* Whether a local is live after the action at a position: the move
     analysis's position after it. *)
  let is_live { block; index } core =
    match Hashtbl.find_opt mir_local core with
    | Some local -> live block (index + 1) local
    | None -> false
  in
  (* Runs [f] on each action at [positions] that some path reaches, with
     what holds before it. *)
  let each_step positions f =
    List.iter
      (fun ({ block; index } as position) ->
        match states.(block) with
        | Some before ->
            List.iteri
              (fun step_index (step : step) ->
                let { views; loans } : state = before.(index).(step_index) in
                f
                  {
                    views;
                    loans = List.concat_map (fun (_, loans) -> List.rev loans) loans;
                    is_live = is_live position;
                    origin = step.origin;
                  }
                  step)
              actions.steps.(block).(index)
        | None -> ())
      positions
  in
  let all_positions =
    List.concat
      (List.mapi
         (fun block positions -> List.init (Array.length positions) (fun index -> { block; index }))
         (Array.to_list actions.steps))
  in
  (* The loans that cover a place, newest first: those that borrow it, and,
     [viewed], those that borrow a holder that stores a view of it. *)
  let covering (here : here) (place : Place.t) =
    List.filter_map
      (fun (loan : loan) ->
        if overlaps loan.borrowed place then Some (loan, false)
        else if
          List.exists
            (fun (viewed : view) -> overlaps viewed.place place)
            (resolve context here.views [ { place = loan.borrowed; copied_out = false } ])
        then Some (loan, true)
        else None)
      here.loans
  in
  let is_mut ((loan : loan), _) = loan.mode = Mut in
  (* The values, by where each is made, whose dangling views are reported:
     a value can end on more than one path. *)
  let dangled = Hashtbl.create 4 in
  (* Reports a use of a place that a [mut] loan covers. *)
  let check_use (here : here) (place : Place.t) =
    match List.find_opt is_mut (covering here place) with
    | Some (loan, viewed) ->
        report context Conflicting_loan (span context here.origin)
          (loan_message context loan ~viewed place ~verb:"be used")
    | None -> ()
  in
  (* Reports a mutation or a move of a place that a loan covers, or that a
     live holder stores a view of. One mutation gets one report. *)
  let check_mutation (here : here) (place : Place.t) ~verb =
    let at = span context here.origin in
    let covering = covering here place in
    match (List.find_opt is_mut covering, covering) with
    | Some (loan, viewed), _ ->
        report context Conflicting_loan at (loan_message context loan ~viewed place ~verb)
    | None, (loan, viewed) :: _ ->
        report context Changed_while_viewed at (loan_message context loan ~viewed place ~verb)
    | None, [] ->
        List.iter
          (fun ((holder : Place.root), viewed) ->
            let in_use =
              match holder with
              | Local local when not (outlives_function context { root = holder; steps = [] }) ->
                  here.is_live local
              | Local _ | Temporary _ | Constant _ | Environment -> true
            in
            if in_use && List.exists (fun (viewed : view) -> overlaps viewed.place place) viewed
            then
              report context Changed_while_viewed at
                (Printf.sprintf "`%s` cannot %s while `%s`, which views it, is still in use."
                   (show context place) verb (show_root context holder)))
          here.views
  in
  each_step all_positions (fun here (step : step) ->
      let at = span context here.origin in
      match step.action with
      | Read place -> check_use here place
      | Mutate place ->
          check_use here place;
          check_mutation here place ~verb:"be borrowed `mut`"
      | Assign place -> check_mutation here place ~verb:"be assigned"
      | Move { place; type_; returned; captured; _ } -> (
          check_use here place;
          match Move_rules.verdict context place ~type_ ~returned ~captured with
          | Moves -> check_mutation here place ~verb:"be moved"
          | Reads -> ()
          | Refused refuse -> refuse context at type_)
      | Move_out_of_lent type_ ->
          report context Not_owned at
            ~fixes:(Move_rules.copy_fix context "Copy it." type_ at)
            "This part is lent, so it cannot be moved: the loan ends when the statement ends. Copy \
             it instead."
      | Arguments { places; views; yielded } ->
          (* Aliasing: two places that one call borrows cannot overlap if
             either is borrowed [mut]. *)
          List.iteri
            (fun first_index (first : borrowed_argument) ->
              List.iteri
                (fun second_index (second : borrowed_argument) ->
                  if
                    second_index > first_index
                    && (first.mode = Mut || second.mode = Mut)
                    && surely_overlap context first.place second.place
                  then
                    let exclusive, also =
                      if first.mode = Mut then (first, second) else (second, first)
                    in
                    report context Conflicting_loan (with_mark context second.at)
                      (Printf.sprintf
                         (if yielded then
                            format_of_string
                              "`%s` is lent `mut` to the yielded value, so `%s` cannot be lent to \
                               it too."
                          else
                            "`%s` is borrowed `mut` by this call, so the call cannot also use `%s`.")
                         (show context exclusive.place) (show context also.place)))
                places)
            places;
          (* Aliasing: a view argument cannot view a place that the call
             borrows [mut], because the callee could mutate the place while
             it reads the view. *)
          List.iter
            (fun (position, viewed, view_at) ->
              let viewed = resolve context here.views viewed in
              List.iter
                (fun (passed : borrowed_argument) ->
                  if
                    passed.position <> position && passed.mode = Mut
                    && List.exists
                         (fun (viewed : view) -> surely_overlap context viewed.place passed.place)
                         viewed
                  then
                    report context Conflicting_loan (with_mark context view_at)
                      (Printf.sprintf
                         "`%s` is borrowed `mut` by this call, so the call cannot also take a view \
                          of it."
                         (show context passed.place)))
                places)
            views
      | Drop dropped ->
          (* A dangling view: a live holder stores a view of a value that
             ends here. A place that outlives the function cannot store a
             view of a local at all, which [Store] reports. *)
          List.iter
            (fun ((root : Place.root), made) ->
              let views_root ((holder : Place.root), viewed) =
                (match holder with
                  | Local local ->
                      here.is_live local
                      && not (outlives_function context { root = holder; steps = [] })
                  | Temporary _ | Constant _ | Environment -> false)
                && List.exists
                     (fun (view : view) -> view.place.root = root && not view.copied_out)
                     viewed
              in
              match List.find_opt views_root here.views with
              | Some (holder, _) when not (Hashtbl.mem dangled made) -> (
                  Hashtbl.replace dangled made ();
                  (* A synthetic local, such as the list that a list
                     literal builds, has no name in the source. *)
                  let named_holder =
                    match holder with
                    | Local local when Hashtbl.mem context.names local ->
                        Some (show_root context holder)
                    | _ -> None
                  in
                  let holder =
                    match named_holder with
                    | Some name -> Printf.sprintf "`%s`" name
                    | None -> "the value built here"
                  in
                  match root with
                  | Temporary _ ->
                      report context Views_temporary (span context made)
                        (Printf.sprintf
                           "This temporary is dropped while %s may still store a view of it, which \
                            would dangle. Bind the temporary to a name with `let`%s, so that it \
                            outlives the view."
                           holder
                           (match named_holder with
                           | Some name -> Printf.sprintf " in the block that declares `%s`" name
                           | None -> ""))
                  | Local _ | Constant _ | Environment ->
                      report context View_escapes (span context made)
                        (Printf.sprintf
                           "`%s` is dropped at the end of its scope while %s may still store a \
                            view of it, which would dangle."
                           (show_root context root) holder))
              | _ -> ())
            dropped
      | Bind_lent_part type_ ->
          report context Keeps_lent_part at
            ~fixes:(Move_rules.copy_fix context "Copy it." type_ at)
            "This part is lent only until the statement ends, so it cannot be bound to a name. Use \
             it in this statement, or copy it."
      | Pass_owned_function views -> (
          (* The callee may store the function, so the function must capture
             nothing. A function value that this function does not own, such
             as a read-only parameter, may be a capturing lambda. *)
          match
            List.find_opt
              (fun (viewed : view) ->
                match viewed.place.root with
                | Environment -> true
                | Temporary _ | Constant _ -> false
                | Local _ -> kind context viewed.place.root <> Owned)
              (resolve context here.views views)
          with
          | Some { place = { root = Environment; _ }; _ } ->
              report context View_escapes at
                "This lambda captures local variables, and the callee may store a function that it \
                 takes through an `own` parameter, so the lambda could outlive them. Pass a \
                 function that captures nothing."
          | Some viewed ->
              report context View_escapes at
                (Printf.sprintf
                   "`%s` is not owned here, so it may be a capturing lambda, and the callee may \
                    store a function that it takes through an `own` parameter. Pass a function \
                    that captures nothing."
                   (show context viewed.place))
          | None -> ())
      | Return_view views ->
          let views = resolve context here.views views in
          (* A caller reaches a capability's implementation only through the
             capability, so the caller's ownership check cannot track a view
             of the implementation's state. The next call could mutate that
             state and invalidate the view. *)
          if
            (not
               (dangles context at ~views ~doing:"returns"
                  ~fix:"A function returns a view only of its parameters."))
            && context.implements_capability
            && List.exists
                 (fun (view : view) -> view.place.root = Local Self && not view.copied_out)
                 views
          then
            report context View_crosses_capability at
              "This returns a view of the capability implementation's own state. The caller cannot \
               see the implementation, so nothing stops the next call from mutating that state \
               while the view is in use. Return a copy."
      | Store { place; views; _ } -> (
          if outlives_function context place then
            let resolved = resolve context here.views views in
            (* The caller assumes that a [mut] argument stores only the
               views that the call was passed as view arguments. So the
               function cannot store there a view of a borrowed parameter
               that is not a view, or a view of the place itself. *)
            let is_self_reference (view : view) =
              view.place.root = place.root && not view.copied_out
            in
            let views_borrowed_parameter (view : view) =
              match view.place.root with
              | Local local when local = Self || List.mem local context.parameters -> (
                  match Hashtbl.find_opt context.types local with
                  | Some type_ -> not (is_view context type_)
                  | None -> false)
              | Local _ | Temporary _ | Constant _ | Environment -> false
            in
            (* The caller of a capability's method cannot see the
               implementation, so the caller's ownership check cannot track
               a view argument that the implementation stores. So the
               implementation stores no view argument. *)
            let stores_argument_view (view : view) =
              context.implements_capability && place.root = Local Self
              &&
              match view.place.root with
              | Local local -> local <> Self && List.mem local context.parameters
              | Temporary _ | Constant _ | Environment -> false
            in
            if
              not
                (dangles context at ~views:resolved
                   ~doing:
                     (Printf.sprintf "stores in `%s`, which outlives this function,"
                        (show_root context place.root))
                   ~fix:"A `mut` parameter stores only views that the function receives.")
            then
              match
                ( List.find_opt stores_argument_view resolved,
                  List.find_opt is_self_reference resolved,
                  List.find_opt views_borrowed_parameter resolved )
              with
              | Some stored_view, _, _ ->
                  report context View_crosses_capability at
                    (Printf.sprintf
                       "This stores a view of `%s` in a capability implementation. The caller \
                        cannot see the implementation, so it could mutate or drop the view's \
                        original while the implementation still stores the view. Store a copy."
                       (show_root context stored_view.place.root))
              | None, Some _, _ ->
                  report context Self_referential at
                    (Printf.sprintf
                       "This stores a view of a part of `%s` in `%s` itself, which makes it \
                        self-referential. The caller does not know about the view, so it could \
                        mutate that part and invalidate the view."
                       (show_root context place.root) (show_root context place.root))
              | None, None, Some parameter ->
                  let parameter = show_root context parameter.place.root in
                  report context View_escapes at
                    (Printf.sprintf
                       "This stores a view of `%s` in `%s`, which outlives this function, but `%s` \
                        is only borrowed for the call, and the caller does not expect it to stay \
                        borrowed afterwards. Take `%s` as a view type, such as a `Slice`, to store \
                        a view of it."
                       parameter (show_root context place.root) parameter parameter)
              | None, None, None -> ())
      | Write_through slice -> (
          (* Writing through a slice mutates the places that the slice
             views, so each of them must be mutable. A slice that is stored
             in a field is read-only, whatever the mode of the record: the
             record's mode does not say whether the viewed place is mutable.
             A slice parameter is writable if its mode is [mut], which the
             type checker checks. *)
          let mutable_root (root : Place.root) =
            match root with
            | Temporary _ -> true
            | Constant _ | Environment -> false
            | Local local -> (
                match kind context root with
                | Borrowed_mut -> true
                | Owned -> List.mem local context.mutable_locals
                | Borrowed -> false)
          in
          match slice with
          | { steps = _ :: _; _ } ->
              report context Read_only_view at
                (Printf.sprintf
                   "`%s` is a slice stored in a field, so it is read-only. Mutate the collection \
                    that it views instead."
                   (show context slice))
          | { root = Local local; _ } when List.mem local context.parameters -> ()
          | _ -> (
              match
                List.find_opt
                  (fun (viewed : view) ->
                    viewed.place <> slice && not (mutable_root viewed.place.root))
                  (resolve context here.views [ { place = slice; copied_out = true } ])
              with
              | Some viewed ->
                  report context Read_only_view at
                    (Printf.sprintf
                       "`%s` views `%s`, which is read-only here, so `%s` cannot be written \
                        through."
                       (show context slice) (show context viewed.place) (show context slice))
              | None -> ()))
      | Yield_point { views; _ } ->
          (* The caller may store a lent view, so a method lends a view only
             of its parameters. *)
          ignore
            (dangles context at
               ~views:(resolve context here.views views)
               ~doing:"lends" ~fix:"A method lends a view only of its parameters.")
      | Bind _ | Bind_views _ | Start_loan _ | End_loans _ -> ());
  (* The places that a range of positions mutates, and the places that it
     uses. A use of a view uses the places that it views, and a write
     through a slice mutates the places that the slice views. *)
  let effects positions =
    let changes = ref [] and uses = ref [] in
    each_step positions (fun here (step : step) ->
        let viewed place =
          List.map
            (fun (view : view) -> view.place)
            (resolve context here.views [ { place; copied_out = true } ])
        in
        match step.action with
        | Read place -> uses := (place :: viewed place) @ !uses
        | Mutate place ->
            uses := (place :: viewed place) @ !uses;
            changes := (place, here.origin) :: !changes
        | Write_through place ->
            changes := List.map (fun viewed -> (viewed, here.origin)) (viewed place) @ !changes
        | Assign place -> changes := (place, here.origin) :: !changes
        | Move { place; type_; returned; captured; _ } -> (
            uses := place :: !uses;
            match Move_rules.verdict context place ~type_ ~returned ~captured with
            | Moves -> changes := (place, here.origin) :: !changes
            | Reads | Refused _ -> ())
        | _ -> ());
    (!changes, !uses)
  in
  (* Data races between the branches of a [parallel] or [concurrent] block:
     a place that one branch mutates must not overlap a place that another
     branch uses. Two elements of one collection may be disjoint, which is
     left to the prover as a [Disjoint] obligation. *)
  List.iter
    (fun ({ keyword; branches } : fork_join_block) ->
      let branches = List.map effects branches in
      List.iteri
        (fun index (changes, _) ->
          List.iteri
            (fun other (other_changes, other_uses) ->
              if other <> index then
                let used = other_uses @ List.map fst other_changes in
                List.iter
                  (fun (place, origin) ->
                    if List.exists (surely_overlap context place) used then
                      report context Data_race (span context origin)
                        (Printf.sprintf
                           "Data race: one branch of this `%s` block mutates `%s`, and another \
                            branch uses it."
                           keyword (show context place)))
                  changes)
            branches)
        branches)
    actions.fork_join_blocks;
  (* Data races between the iterations of a [parallel for] or [concurrent
     for]: the body can mutate only the locals of one iteration, which are
     the loop's pattern variables, the locals that the body binds, and the
     temporaries that it makes. *)
  List.iter
    (fun ({ keyword; body; bound; temporaries } : fork_join_loop) ->
      let bound = ref bound in
      each_step body (fun _ (step : step) ->
          match step.action with Bind locals -> bound := locals @ !bound | _ -> ());
      List.iter
        (fun ((place : Place.t), origin) ->
          let outside =
            match place.root with
            | Constant _ | Environment | Local Self -> true
            | Local local -> not (List.mem local !bound)
            | Temporary local -> not (List.mem local temporaries)
          in
          if outside then
            report context Data_race (span context origin)
              (Printf.sprintf
                 "Data race: the iterations of a `%s for` run at the same time, so the body can \
                  mutate only its own element and its own locals."
                 keyword))
        (fst (effects body)))
    actions.fork_join_loops

(* Checks the loans and views of a definition's body, then of each of its
   lambdas', with [moves], the move analysis of each body. [returns] says
   whether the definition's body returns to a caller. *)
let check context ~(moves : Mir.body -> Moves.t) ~returns (mir : Mir.t) =
  let builder =
    {
      context;
      moves = moves mir.body;
      body = mir.body;
      captured = [];
      held = Hashtbl.create 32;
      returned = [];
      aliases = [];
      binding = [];
      storage_lend = false;
      keeps_lent = [];
      loop_entries = Hashtbl.create 4;
      loop_elements = [];
      position = { block = 0; index = 0 };
      written = [];
    }
  in
  check_body context (of_body builder mir.body ~returns) (moves mir.body);
  Array.iter
    (fun (lambda : Mir.body) ->
      builder.moves <- moves lambda;
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
      check_body context (of_body builder lambda ~returns:false) (moves lambda))
    mir.lambdas
