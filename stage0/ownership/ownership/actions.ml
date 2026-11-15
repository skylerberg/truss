open Context

type view = Borrow_of of Place.t | Copy_of_view_in of Place.t

let viewed_place = function Borrow_of place | Copy_of_view_in place -> place

type loan = { borrowed : Place.t; mode : Types.mode; duration : Mir.loan_duration }

type borrowed_argument = {
  place : Place.t;
  mode : Types.mode;
  origin : Core.origin;
  position : int;
}

type view_argument = { position : int; views : view list; origin : Core.origin }
type dropped_owner = { owner : Place.root; origin : Core.origin }

type action =
  | Read of Place.t
  | Move of { place : Place.t; type_ : Types.ty; is_returned : bool; is_captured : bool }
  | Move_out_of_lent of Types.ty
  | Mutate of Place.t
  | Assign of Place.t
  | Bind of Core.local list
  | Yield_point of { views : view list; parts : Place.t list; forwarded : view list }
  | Bind_views of { locals : Core.local list; views : view list }
  | Store of { place : Place.t; views : view list; replaces_root : bool }
  | Return_view of view list
  | Drop of dropped_owner list
  | Bind_lent_part of Types.ty
  | Pass_owned_function of view list
  | Start_loan of { loan : int; loans : loan list }
  | End_loans of int list
  | Write_through of Place.t
  | Arguments of {
      borrowed_arguments : borrowed_argument list;
      view_arguments : view_argument list;
      is_yielded : bool;
    }

type position = { block : Mir.Graph.block; index : int }
type step = { action : action; origin : Core.origin }
type fork_join_block = { keyword : string; branches : position list list }

type fork_join_loop = {
  keyword : string;
  body : position list;
  pattern_locals : Core.local list;
  temporaries : Mir.local list;
}

type t = {
  body : Mir.Graph.body;
  steps : step list array array;
  fork_join_blocks : fork_join_block list;
  fork_join_loops : fork_join_loop list;
}

type held = {
  place : Place.t option;
  views : view list;
  slice : Place.t option;
  lent : Place.t option list;
  collection : (Place.t option * Types.ty) option;
  owns_new_value : bool;
  alias : Mir.place option;
  is_loop_part : bool;
}

let nothing =
  {
    place = None;
    views = [];
    slice = None;
    lent = [];
    collection = None;
    owns_new_value = true;
    alias = None;
    is_loop_part = false;
  }

type lent_part_binding = {
  binding : Mir.local;
  part : Mir.local;
  part_type : Types.ty;
  origin : Core.origin;
}

type builder = {
  context : Context.context;
  moves : Moves.t;
  body : Mir.Graph.body;
  captured : Core.local list;
  held : (Mir.local, held) Hashtbl.t;
  returned_temporaries : Mir.local list;
  loop_elements : Mir.local list;
  loop_body_starts : (Mir.Graph.block, int) Hashtbl.t;
  mutable aliases : Mir.local list;
  mutable unassigned_locals : Mir.local list;
  mutable element_receivers : Core.origin list;
  mutable lent_part_bindings : lent_part_binding list;
  mutable position : position;
  mutable written : step list;
}

let emit builder action origin = builder.written <- { action; origin } :: builder.written
let held builder local = Option.value ~default:nothing (Hashtbl.find_opt builder.held local)
let local_info builder local = builder.body.locals.(local)

let core_local builder (local : Mir.local) =
  match (local_info builder local).kind with
  | Source { local; _ } -> Some local
  | Temporary | Lent _ -> None

let tracked builder (place : Mir.place) : Place.t option =
  let base =
    match place.root with
    | Constant path -> Some { Place.root = Constant path; steps = [] }
    | Local local -> (
        match core_local builder local with
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

let is_untracked_lent_part builder (place : Mir.place) =
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

let views_of_copy builder (place : Mir.place) =
  match tracked builder place with
  | Some place -> [ Copy_of_view_in place ]
  | None -> ( match place.root with Local local -> (held builder local).views | Constant _ -> [])

let views_of_borrow builder (place : Mir.place) type_ =
  match tracked builder place with
  | Some place ->
      [ (if plain builder.context type_ then Copy_of_view_in place else Borrow_of place) ]
  | None -> (
      match (place.root, temporary_of builder place) with
      | Local _, Some temporary
        when (held builder temporary).owns_new_value
             && (not (plain builder.context type_))
             && not (is_view builder.context type_) ->
          [ Borrow_of { root = Temporary temporary; steps = [] } ]
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

let views_of_argument builder (mode : Types.mode) (operand : Mir.operand) =
  match operand with
  | Use { place; type_; _ } when mode <> Own -> views_of_borrow builder place type_
  | _ -> views_of_operand builder operand

let views_of_part builder (operand : Mir.operand) =
  match operand_type operand with
  | Some type_ when is_view builder.context type_ -> views_of_operand builder operand
  | _ -> []

let operand_borrows builder (operand : Mir.operand) =
  match operand with
  | Borrow { place; _ } -> Option.to_list (tracked builder place)
  | Use { type_; _ } when is_view builder.context type_ ->
      List.map viewed_place (views_of_operand builder operand)
  | Use _ | Take _ | Constant _ -> []

let result_may_view builder (mode : Types.mode) type_ =
  (mode <> Own && not (plain builder.context type_)) || is_view builder.context type_

let viewable_argument builder (argument : Mir.argument) =
  match argument with
  | Passed { mode; value; _ } -> (
      match operand_type value with
      | Some type_ when result_may_view builder mode type_ -> Some (mode, value)
      | _ -> None)
  | Default -> None

let viewable_arguments builder (call : Mir.call) =
  List.filter_map (viewable_argument builder) call.arguments

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
    (fun slice -> emit builder (Write_through slice) origin)
    (written_slice builder ~whole place type_)

let is_captured builder (place : Place.t) =
  match place.root with
  | Local local -> List.mem local builder.captured
  | Temporary _ | Constant _ | Environment -> false

let evaluate builder ~is_returned (use : Moves.use) =
  let read place origin =
    Option.iter (fun tracked -> emit builder (Read tracked) origin) (tracked builder place)
  in
  match use.operand with
  | Some (Use { place; type_; origin; _ } | Borrow { place; type_; origin; _ }) when use.moves -> (
      match tracked builder place with
      | Some tracked ->
          emit builder
            (Move { place = tracked; type_; is_returned; is_captured = is_captured builder tracked })
            origin
      | None ->
          if is_untracked_lent_part builder place then emit builder (Move_out_of_lent type_) origin)
  | Some (Use { place; origin; _ } | Take { place; origin; _ }) -> read place origin
  | Some (Borrow { place; mode = Read | Own; origin; _ }) -> (
      match place.root with
      | Local local when List.mem local builder.aliases -> ()
      | _ -> read place origin)
  | None -> read use.place use.origin
  | Some (Borrow { mode = Mut; _ } | Constant _) -> ()

let borrow_mut builder (operand : Mir.operand) =
  match operand with
  | Borrow { place; type_; mode = Mut; origin } ->
      writes_through builder ~whole:true place type_ origin;
      Option.iter (fun tracked -> emit builder (Mutate tracked) origin) (tracked builder place)
  | Use { place; origin; _ } -> (
      match place.root with
      | Local local ->
          Option.iter (fun slice -> emit builder (Mutate slice) origin) (held builder local).slice
      | Constant _ -> ())
  | _ -> ()

let call builder (call : Mir.call) origin =
  List.iter
    (function
      | Mir.Passed { mode = Mut; value; _ } -> borrow_mut builder value | Passed _ | Default -> ())
    call.arguments;
  let borrowed_arguments =
    List.concat
      (List.mapi
         (fun position (argument : Mir.argument) ->
           match argument with
           | Passed { mode; value = Borrow { place; origin; _ }; _ } -> (
               match tracked builder place with
               | Some place -> [ { place; mode; origin; position } ]
               | None -> [])
           | Passed { mode = Mut; value = Use { place = { root = Local local; _ }; origin; _ }; _ }
             -> (
               match (held builder local).slice with
               | Some place -> [ { place; mode = Mut; origin; position } ]
               | None -> [])
           | Passed _ | Default -> [])
         call.arguments)
  in
  let view_arguments =
    List.concat
      (List.mapi
         (fun position (argument : Mir.argument) ->
           match argument with
           | Passed { value = (Use { type_; origin; _ } | Borrow { type_; origin; _ }) as value; _ }
             when is_view builder.context type_ ->
               [ { position; views = views_of_operand builder value; origin } ]
           | Passed _ | Default -> [])
         call.arguments)
  in
  if List.length borrowed_arguments > 1 || (borrowed_arguments <> [] && view_arguments <> []) then
    emit builder (Arguments { borrowed_arguments; view_arguments; is_yielded = false }) origin;
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
              emit builder
                (Store
                   {
                     place;
                     views = List.concat_map (views_of_operand builder) others;
                     replaces_root = false;
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
          emit builder (Pass_owned_function (views_of_operand builder value)) origin
      | _ -> ())
    call.arguments

let call_result builder (call : Mir.call) =
  {
    nothing with
    views =
      List.concat_map
        (fun (mode, value) -> views_of_argument builder mode value)
        (viewable_arguments builder call);
  }

let lent_part builder (call : Mir.call) ~part_type =
  if is_view builder.context part_type then call_result builder call
  else
    let receiver =
      match call.arguments with first :: _ -> viewable_argument builder first | [] -> None
    in
    match receiver with
    | Some (mode, receiver) -> { nothing with views = views_of_argument builder mode receiver }
    | None -> nothing

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
          owns_new_value = known.owns_new_value && value.owns_new_value;
          alias = (match value.alias with Some _ -> value.alias | None -> known.alias);
          is_loop_part = known.is_loop_part || value.is_loop_part;
        }
  | _ -> ()

let lent_places builder (operand : Mir.operand) =
  match operand with
  | Borrow { place; _ } -> [ tracked builder place ]
  | Use { place = { root = Local local; projections = [] }; _ }
    when (local_info builder local).kind = Temporary ->
      (held builder local).lent
  | Use _ | Take _ | Constant _ -> []

let rvalue builder (value : Mir.rvalue) : held =
  match value with
  | Operand operand ->
      let views = views_of_operand builder operand in
      let lent = lent_places builder operand in
      let slice, owns_new_value =
        match operand with
        | Use { place = { root = Local local; _ } as place; _ } when is_temporary builder place ->
            ((held builder local).slice, (held builder local).owns_new_value)
        | Use _ | Take _ | Borrow _ -> (None, false)
        | Constant _ -> (None, false)
      in
      {
        nothing with
        views;
        lent = (match operand with Borrow _ -> [] | _ -> lent);
        slice;
        owns_new_value;
      }
  | Operation _ | Compare _ -> nothing
  | Not operand | Convert { value = operand; _ } | To_any { value = operand; _ } | Copy operand ->
      { nothing with views = views_of_operand builder operand }
  | Construct { fields; _ } ->
      let supplied = List.filter_map snd fields in
      {
        nothing with
        views = List.concat_map (views_of_part builder) supplied;
        lent = List.concat_map (lent_places builder) supplied;
      }
  | Array elements -> { nothing with views = List.concat_map (views_of_part builder) elements }
  | Is_variant _ -> nothing
  | Lambda { captures; _ } -> (
      match captures with
      | [] -> { nothing with owns_new_value = false }
      | _ ->
          {
            nothing with
            owns_new_value = false;
            views =
              Borrow_of { root = Environment; steps = [] }
              :: List.map
                   (fun (capture : Mir.capture) ->
                     Borrow_of { root = Local capture.local; steps = [] })
                   captures;
          })
  | Function_value _ | Value_parameter _ | Conditional _ | Cases _ | Connective _ | Specification _
    ->
      nothing

let bound_value builder (local : Mir.local) (core : Core.local) (value : Mir.rvalue) origin ~is_var
    =
  let type_ = (local_info builder local).type_ in
  let holds_views = is_view builder.context type_ in
  let result = rvalue builder value in
  let is_loop_part (place : Mir.place) =
    match place.root with Local part -> (held builder part).is_loop_part | Constant _ -> false
  in
  (match value with
  | Operand
      (Borrow { place = { root = Local part; _ } as place; type_ = part_type; origin = at; _ })
    when (not is_var)
         && is_untracked_lent_part builder place
         && (not (is_loop_part place))
         && ((not (plain builder.context part_type)) || is_view builder.context part_type) ->
      builder.lent_part_bindings <-
        { binding = local; part; part_type; origin = at } :: builder.lent_part_bindings
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
  let is_copy_of_loop_part =
    plain builder.context type_
    &&
    match value with
    | Operand (Use { place; _ } | Borrow { place; _ }) -> is_loop_part place
    | _ -> false
  in
  let views =
    if is_copy_of_loop_part then List.map (fun view -> Copy_of_view_in (viewed_place view)) views
    else views
  in
  if holds_views || views <> [] then emit builder (Bind_views { locals = [ core ]; views }) origin

let returned_temporaries (body : Mir.Graph.body) =
  let returned = ref [] in
  Array.iter
    (fun (block : Mir.Graph.basic_block) ->
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
      (fun (block : Mir.Graph.basic_block) ->
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

let loans_of builder (borrowed : Mir.operand) mode duration : loan list =
  List.map (fun borrowed : loan -> { borrowed; mode; duration }) (operand_borrows builder borrowed)

let read_uses builder ?(is_returned = fun _ -> false) ?(skip = fun _ -> false) uses =
  List.iter
    (fun (use : Moves.use) ->
      if not (skip use) then evaluate builder ~is_returned:(is_returned use) use)
    uses

let statement builder (statement : Mir.statement) =
  let origin = statement.origin in
  let uses = Moves.statement_uses builder.moves statement in
  match statement.kind with
  | Live locals ->
      builder.unassigned_locals <- locals @ builder.unassigned_locals;
      let core = List.filter_map (core_local builder) locals in
      if core <> [] then emit builder (Bind core) origin
  | Dead locals ->
      List.iter
        (fun (bound : lent_part_binding) ->
          if List.mem bound.part locals && not (List.mem bound.binding locals) then
            emit builder (Bind_lent_part bound.part_type) bound.origin)
        builder.lent_part_bindings;
      let dropped =
        List.filter_map
          (fun local ->
            let info = local_info builder local in
            match info.kind with
            | Temporary -> Some { owner = Place.Temporary local; origin = info.origin }
            | Source { local = core; mode = Own; _ } ->
                Some { owner = Place.Local core; origin = info.origin }
            | Source _ | Lent _ -> None)
          locals
      in
      if dropped <> [] then emit builder (Drop dropped) origin;
      builder.lent_part_bindings <-
        List.filter
          (fun (bound : lent_part_binding) ->
            not (List.mem bound.binding locals || List.mem bound.part locals))
          builder.lent_part_bindings
  | Assign { target = { root = Local local; projections = [] } as target; value; _ }
    when List.mem local builder.unassigned_locals
         ||
         match (local_info builder local).kind with
         | Temporary -> true
         | Lent _ -> not (Hashtbl.mem builder.held local)
         | Source _ -> false -> (
      builder.unassigned_locals <-
        List.filter (fun unassigned -> unassigned <> local) builder.unassigned_locals;
      match (local_info builder local).kind with
      | Temporary -> (
          match value with
          | Operand (Use { place; _ })
            when List.mem local builder.returned_temporaries
                 && Option.is_some (tracked builder place) ->
              read_uses builder ~is_returned:(fun _ -> true) uses;
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
                  owns_new_value = false;
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
          emit builder (Assign place) origin;
          match type_ with
          | Some type_ when is_view builder.context type_ ->
              emit builder
                (Store { place; views = result.views; replaces_root = place.steps = [] })
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
      let is_loop_element = List.mem part builder.loop_elements in
      let element_of collection collection_type ~receiver =
        if is_untracked_lent_part builder collection then None
        else
          let collection_place = tracked builder collection in
          Some
            ( Option.map
                (fun (place : Place.t) ->
                  { place with steps = place.steps @ [ Element { node = called.node; origin } ] })
                collection_place,
              (collection_place, collection_type),
              receiver )
      in
      let element =
        match (called.callee, called.arguments) with
        | ( Trait_method { trait; name = "at"; self_type; _ },
            Passed
              {
                value = Borrow { place = collection; type_ = collection_type; origin = receiver; _ };
                _;
              }
            :: _ )
          when (Well_known.is Index trait.trait || Well_known.is Index_mut trait.trait)
               && Place.is_storage_type self_type ->
            element_of collection collection_type ~receiver
        | ( ( Trait_method { name = "element"; _ }
            | Function { path = Method { name = "element"; _ }; _ } ),
            Passed
              {
                value = Borrow { place = collection; type_ = collection_type; origin = receiver; _ };
                _;
              }
            :: _ )
          when is_loop_element && Place.is_storage_type collection_type ->
            element_of collection collection_type ~receiver
        | _ -> None
      in
      match element with
      | Some (place, collection, receiver) ->
          read_uses builder uses;
          builder.element_receivers <- receiver :: builder.element_receivers;
          hold builder
            { Mir.root = Local part; projections = [] }
            { nothing with place; collection = Some collection }
      | None ->
          read_uses builder uses;
          call builder called origin;
          hold builder
            { Mir.root = Local part; projections = [] }
            {
              (lent_part builder called ~part_type:(local_info builder part).type_) with
              is_loop_part = is_loop_element;
            })
  | Slice { destination; base; call = called } ->
      read_uses builder uses;
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
        match (elements, base_type) with
        | Some place, Some base_type when Place.is_slice_type base_type -> [ Copy_of_view_in place ]
        | Some place, _ -> [ Borrow_of place ]
        | None, _ -> views_of_borrow builder base (Option.value ~default:Types.unit base_type)
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
        match (duration, borrowed) with
        | Rest_of_statement, Borrow { origin = receiver; _ }
          when List.mem receiver builder.element_receivers ->
            []
        | _ -> loans_of builder borrowed mode duration
      in
      emit builder (Start_loan { loan; loans }) origin;
      if duration = Loop_body then
        Hashtbl.replace builder.loop_body_starts builder.position.block (builder.position.index + 1)
  | Loan_end loans -> emit builder (End_loans loans) origin
  | Provide_end | Ghost_assert _ | Matched _ | Proof _ -> ()
  | While _ | For _ | Fork _ | Resume _ | Yield _ | Jump _ ->
      Compiler_bug.bug ~stage:"Ownership" "a statement of a MIR graph that is a block or a jump"

let pull builder (iteration : Mir.iteration) origin =
  match iteration with
  | Pull { cursor; _ } ->
      Option.iter (fun tracked -> emit builder (Mutate tracked) origin) (tracked builder cursor)
  | Range _ -> ()

let terminator builder ~returns_to_caller (basic : Mir.Graph.basic_block) =
  let origin = basic.terminator_origin in
  let uses = Moves.terminator_uses builder.moves basic in
  let returning value =
    read_uses builder
      ~is_returned:(fun (use : Moves.use) ->
        match use.operand with
        | Some (Use { place; _ }) -> not (is_temporary builder place)
        | _ -> false)
      uses;
    match value with
    | Some value -> (
        match operand_type value with
        | Some type_ when returns_to_caller && is_view builder.context type_ ->
            emit builder (Return_view (views_of_operand builder value)) origin
        | _ -> ())
    | None -> ()
  in
  match basic.terminator with
  | Branch _ -> read_uses builder uses
  | For { iteration; part; _ } -> (
      let part_place = { Mir.root = Local part; projections = [] } in
      match iteration with
      | Range _ -> read_uses builder uses
      | Pull { cursor; _ } ->
          pull builder iteration origin;
          hold builder part_place
            { nothing with views = views_of_copy builder cursor; owns_new_value = true })
  | Yield { mode; part; _ } ->
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
          (fun lent -> Option.iter (fun place -> emit builder (Mutate place) origin) lent)
          lent;
        let borrowed_arguments =
          List.concat
            (List.mapi
               (fun position lent ->
                 match lent with Some place -> [ { place; mode; origin; position } ] | None -> [])
               lent)
        in
        if List.length borrowed_arguments > 1 then
          emit builder
            (Arguments { borrowed_arguments; view_arguments = []; is_yielded = true })
            origin
      end;
      let lent_by_address (operand : Mir.operand) =
        match operand with
        | Use { place; type_; _ } | Borrow { place; type_; _ } | Take { place; type_; _ } ->
            if plain builder.context type_ then None else Some place
        | Constant _ -> None
      in
      let parts =
        List.filter_map
          (fun leaf -> Option.bind (lent_by_address leaf) (tracked builder))
          (leaves part)
      in
      let forwarded =
        List.concat_map
          (fun (leaf : Mir.operand) ->
            match (lent_by_address leaf, operand_type leaf) with
            | Some place, Some type_
              when is_untracked_lent_part builder place && not (is_view builder.context type_) ->
                views_of_operand builder leaf
            | _ -> [])
          (leaves part)
      in
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
      emit builder (Yield_point { views; parts; forwarded }) origin
  | Return value -> returning value
  | Cancel { returned; _ } -> returning (Option.map fst returned)
  | Iteration_end { loop } -> (
      match builder.body.blocks.(loop).terminator with
      | For { iteration; _ } -> pull builder iteration origin
      | _ -> ())
  | Join _ | Goto _ | Fork _ | Resume _ | Unreachable | Written_unreachable | Todo -> ()

let of_body context moves (body : Mir.Graph.body) ~returns_to_caller : t =
  let builder =
    {
      context;
      moves;
      body;
      captured =
        List.filter_map
          (fun local ->
            match body.locals.(local).kind with
            | Source { local = core; _ } -> Some core
            | Temporary | Lent _ -> None)
          body.captures;
      held = Hashtbl.create 32;
      returned_temporaries = returned_temporaries body;
      loop_elements =
        Array.to_list body.blocks
        |> List.filter_map (fun (basic : Mir.Graph.basic_block) ->
            match basic.terminator with
            | For { lent = Some { element; _ }; _ } -> Some element
            | _ -> None);
      loop_body_starts = Hashtbl.create 4;
      aliases = [];
      unassigned_locals = [];
      element_receivers = [];
      lent_part_bindings = [];
      position = { block = 0; index = 0 };
      written = [];
    }
  in
  let shape =
    Array.map (fun (basic : Mir.Graph.basic_block) -> List.length basic.statements + 1) body.blocks
  in
  let steps = Array.map (fun count -> Array.make count []) shape in
  let write position body =
    builder.position <- position;
    body ();
    steps.(position.block).(position.index) <- List.rev builder.written;
    builder.written <- []
  in
  Array.iteri
    (fun block (basic : Mir.Graph.basic_block) ->
      List.iteri
        (fun index statement' -> write { block; index } (fun () -> statement builder statement'))
        basic.statements;
      write
        { block; index = List.length basic.statements }
        (fun () -> terminator builder ~returns_to_caller basic))
    body.blocks;
  let is_terminator { block; index } = index = List.length body.blocks.(block).statements in
  let positions_of ?(from = fun _ -> None) blocks =
    List.concat_map
      (fun block ->
        let first = Option.value ~default:0 (from block) in
        List.init (max 0 (shape.(block) - first)) (fun offset -> { block; index = first + offset }))
      (List.sort_uniq compare blocks)
  in
  let fork_join_blocks =
    Array.to_list body.blocks
    |> List.filter_map (fun (basic : Mir.Graph.basic_block) ->
        match basic.terminator with
        | Fork { concurrent; branches; _ } ->
            Some
              {
                keyword = (if concurrent then "concurrent" else "parallel");
                branches =
                  List.map (fun (branch : Mir.Graph.branch) -> positions_of branch.blocks) branches;
              }
        | _ -> None)
  in
  let fork_join_loops =
    Array.to_list (Array.mapi (fun block basic -> (block, basic)) body.blocks)
    |> List.filter_map (fun (loop_block, (basic : Mir.Graph.basic_block)) ->
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
                    (fun position ->
                      (not (is_terminator position))
                      || Mir.Graph.iteration_loop body.blocks.(position.block).terminator
                         <> Some loop_block)
                    (positions_of
                       ~from:(fun block ->
                         if block = inside then Hashtbl.find_opt builder.loop_body_starts inside
                         else None)
                       blocks);
                pattern_locals =
                  List.concat_map
                    (fun (statement : Mir.statement) ->
                      match statement.kind with
                      | Live locals -> List.filter_map (core_local builder) locals
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
