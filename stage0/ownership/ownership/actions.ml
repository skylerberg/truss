type view = Borrow_of of Place.t | Copy_of_view_in of Place.t

let extract_viewed_place = function Borrow_of place | Copy_of_view_in place -> place

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
  | Bind_lent_part of { scrutinee : Core.origin; lent_part_type : Types.ty }
  | Pass_owned_function of view list
  | Start_loan of { loan : int; loans : loan list }
  | End_loans of int list
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

type held =
  | Alias of Mir.place
  | Value of { views : view list; lent : Place.t list }
  | Lent_part of { views : view list; is_loop_part : bool }

let make_value views = Value { views; lent = [] }

type reach = Place_of of view | Views of view list

let list_reach_views = function Place_of view -> [ view ] | Views views -> views

type lent_part_binding = {
  binding : Mir.local;
  part : Mir.local;
  origin : Core.origin;
  scrutinee : Core.origin;
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
  mutable unassigned_locals : Mir.local list;
  mutable lent_part_bindings : lent_part_binding list;
  mutable position : position;
  mutable written : step list;
}

let raise_bug message = Compiler_bug.raise_bug ~stage:"Ownership" message
let emit builder action origin = builder.written <- { action; origin } :: builder.written
let lookup_local_info (builder : builder) local = builder.body.locals.(local)

let find_core_local builder (local : Mir.local) =
  match (lookup_local_info builder local).kind with
  | Source { local; _ } -> Some local
  | Temporary | Lent _ -> None

let union known added = known @ List.filter (fun item -> not (List.mem item known)) added

let list_held_views (held : held) =
  match held with
  | Value { views; _ } | Lent_part { views; _ } -> views
  | Alias _ -> raise_bug "the views of a local that stands for a place"

let merge_held (known : held) (value : held) : held =
  if known = value then value
  else
    match (known, value) with
    | Value known, Value value ->
        Value { views = union known.views value.views; lent = union known.lent value.lent }
    | Lent_part part, Value value -> Lent_part { part with views = union part.views value.views }
    | (Alias _ | Value _ | Lent_part _), _ -> raise_bug "a local assigned values of two kinds"

let hold builder (place : Mir.place) (value : held) =
  match place with
  | { root = Local local; projections = [] } ->
      Hashtbl.replace builder.held local
        (match Hashtbl.find_opt builder.held local with
        | Some known -> merge_held known value
        | None -> value)
  | _ -> ()

let rec resolve_alias builder (place : Mir.place) : Mir.place =
  match place.root with
  | Local local -> (
      match Hashtbl.find_opt builder.held local with
      | Some (Alias aliased) ->
          let aliased = resolve_alias builder aliased in
          { aliased with projections = aliased.projections @ place.projections }
      | _ -> place)
  | Constant _ | Literal _ -> place

let is_alias builder local =
  match Hashtbl.find_opt builder.held local with Some (Alias _) -> true | _ -> false

let find_held_root builder (place : Mir.place) =
  match (resolve_alias builder place).root with
  | Local local -> Option.map (fun held -> (local, held)) (Hashtbl.find_opt builder.held local)
  | Constant _ | Literal _ -> None

let track_place builder (place : Mir.place) : Place.t option =
  let place = resolve_alias builder place in
  let base =
    match place.root with
    | Constant path -> Some { Place.root = Constant path; steps = [] }
    | Literal _ -> None
    | Local local -> (
        match (find_core_local builder local, Hashtbl.find_opt builder.held local) with
        | Some local, _ -> Some { Place.root = Local local; steps = [] }
        | None, _
          when Mir.is_in_sequence place && (lookup_local_info builder local).kind = Temporary ->
            Some { Place.root = Temporary local; steps = [] }
        | None, _ -> None)
  in
  Option.map
    (fun (base : Place.t) ->
      List.fold_left
        (fun (place : Place.t) (projection : Mir.projection) ->
          match projection with
          | Field field -> { place with steps = place.steps @ [ Field field ] }
          | Variant_field _ -> place
          | Element { origin; _ } -> { place with steps = place.steps @ [ Element origin ] }
          | Range { origin; _ } -> { place with steps = place.steps @ [ Range origin ] })
        base place.projections)
    base

let find_untracked_lent_part builder (place : Mir.place) =
  match find_held_root builder place with Some (local, Lent_part _) -> Some local | _ -> None

let is_loop_part builder (place : Mir.place) =
  match find_held_root builder place with
  | Some (_, Lent_part { is_loop_part; _ }) -> is_loop_part
  | _ -> false

let is_temporary builder (place : Mir.place) =
  match (resolve_alias builder place).root with
  | Local local -> (lookup_local_info builder local).kind = Temporary
  | Constant _ | Literal _ -> false

let access_place builder (place : Mir.place) ~(borrowed_as : Types.ty option) =
  let place = resolve_alias builder place in
  let ranges_an_owner =
    match List.rev place.projections with
    | Range { sequence; _ } :: _ -> not (Context.is_view builder.context sequence)
    | (Element _ | Field _ | Variant_field _) :: _ | [] -> false
  in
  match (track_place builder place, borrowed_as) with
  | Some tracked, None when ranges_an_owner -> Views [ Borrow_of tracked ]
  | Some tracked, None -> Views [ Copy_of_view_in tracked ]
  | Some tracked, Some type_ ->
      Place_of
        (if Context.lends_nothing builder.context type_ && not ranges_an_owner then
           Copy_of_view_in tracked
         else Borrow_of tracked)
  | None, _ -> (
      match place.root with
      | Constant _ | Literal _ -> Views []
      | Local local -> (
          let is_owned_temporary =
            (lookup_local_info builder local).kind = Temporary
            &&
            match borrowed_as with
            | Some type_ ->
                (not (Context.lends_nothing builder.context type_))
                && not (Context.is_view builder.context type_)
            | None -> false
          in
          match Hashtbl.find_opt builder.held local with
          | (Some (Value _) | None) when is_owned_temporary ->
              Views [ Borrow_of { root = Temporary local; steps = [] } ]
          | Some (Value { views; _ } | Lent_part { views; _ }) -> Views views
          | None -> Views []
          | Some (Alias _) -> raise_bug "an untracked local that names a place"))

let list_copy_views builder place = list_reach_views (access_place builder place ~borrowed_as:None)

let access_operand builder ~is_use_by_reference (operand : Mir.operand) =
  match operand with
  | Borrow { place; type_; _ } -> access_place builder place ~borrowed_as:(Some type_)
  | Use { place; type_; _ } ->
      access_place builder place ~borrowed_as:(if is_use_by_reference then Some type_ else None)
  | Take { place; _ } -> access_place builder place ~borrowed_as:None
  | Immediate _ -> Views []

let access_value builder operand = access_operand builder ~is_use_by_reference:false operand

let access_argument builder (mode : Types.mode) operand =
  access_operand builder ~is_use_by_reference:(mode <> Own) operand

let find_reached_place = function
  | Place_of view -> Some (extract_viewed_place view)
  | Views _ -> None

let find_operand_type : Mir.operand -> Types.ty option = function
  | Use { type_; _ } | Borrow { type_; _ } | Take { type_; _ } -> Some type_
  | Immediate _ -> None

let find_operand_place : Mir.operand -> Mir.place option = function
  | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> Some place
  | Immediate _ -> None

let find_operand_origin : Mir.operand -> Core.origin option = function
  | Use { origin; _ } | Borrow { origin; _ } | Take { origin; _ } -> Some origin
  | Immediate _ -> None

let is_view_operand builder operand =
  match find_operand_type operand with
  | Some type_ -> Context.is_view builder.context type_
  | None -> false

let list_operand_views builder operand = list_reach_views (access_value builder operand)

let list_argument_views builder mode operand =
  list_reach_views (access_argument builder mode operand)

let list_given_views builder (operand : Mir.operand) =
  match operand with
  | (Use _ | Take _) when not (is_view_operand builder operand) -> []
  | Use _ | Take _ | Borrow _ | Immediate _ -> list_operand_views builder operand

let find_lent_place builder (mode : Types.mode) operand =
  match access_argument builder mode operand with
  | Place_of view -> Some (extract_viewed_place view)
  | Views _ -> None

let find_stored_type builder (mode : Types.mode) operand =
  match (access_argument builder mode operand, find_operand_type operand) with
  | Place_of _, Some (Named { path; arguments = Type element :: _ }) when Well_known.is Slice path
    ->
      Some element
  | Place_of _, type_ -> type_
  | Views _, _ -> None

let list_lent_places builder (operand : Mir.operand) =
  match (access_value builder operand, operand) with
  | Place_of view, _ -> [ extract_viewed_place view ]
  | Views _, Use { place = { root = Local local; projections = [] }; _ } -> (
      match Hashtbl.find_opt builder.held local with Some (Value { lent; _ }) -> lent | _ -> [])
  | Views _, (Use _ | Borrow _ | Take _ | Immediate _) -> []

let result_may_view builder (mode : Types.mode) type_ =
  (mode <> Own && not (Context.lends_nothing builder.context type_))
  || Context.is_view builder.context type_

let find_viewable_argument builder (argument : Mir.argument) =
  match argument with
  | Passed { mode; value; _ } -> (
      match find_operand_type value with
      | Some type_ when result_may_view builder mode type_ -> Some (mode, value)
      | _ -> None)
  | Default -> None

let list_viewable_arguments builder (call : Mir.call) =
  List.filter_map (find_viewable_argument builder) call.arguments

let is_captured builder (place : Place.t) =
  match place.root with
  | Local local -> List.mem local builder.captured
  | Temporary _ | Constant _ | Environment -> false

let evaluate builder ~is_returned (use : Moves.use) =
  let read place origin =
    Option.iter (fun tracked -> emit builder (Read tracked) origin) (track_place builder place)
  in
  match use.operand with
  | Some (Use { place; type_; origin; _ } | Borrow { place; type_; origin; _ }) when use.moves -> (
      match track_place builder place with
      | Some tracked ->
          emit builder
            (Move { place = tracked; type_; is_returned; is_captured = is_captured builder tracked })
            origin
      | None ->
          if Option.is_some (find_untracked_lent_part builder place) then
            emit builder (Move_out_of_lent type_) origin)
  | Some (Use { place; origin; _ } | Take { place; origin; _ }) -> read place origin
  | Some (Borrow { place; mode = Read | Own; origin; _ }) -> (
      match place.root with Local local when is_alias builder local -> () | _ -> read place origin)
  | None -> read use.place use.origin
  | Some (Borrow { mode = Mut; _ } | Immediate _) -> ()

let borrow_mut builder (operand : Mir.operand) =
  Option.iter
    (fun origin ->
      Option.iter
        (fun place -> emit builder (Mutate place) origin)
        (find_reached_place (access_argument builder Mut operand)))
    (find_operand_origin operand)

let emit_call builder (call : Mir.call) origin =
  List.iter
    (function
      | Mir.Passed { mode = Mut; value; _ } -> borrow_mut builder value | Passed _ | Default -> ())
    call.arguments;
  let borrowed_arguments =
    List.concat
      (List.mapi
         (fun position (argument : Mir.argument) ->
           match argument with
           | Passed { mode; value; _ } -> (
               match (find_lent_place builder mode value, find_operand_origin value) with
               | Some place, Some origin -> [ { place; mode; origin; position } ]
               | _ -> [])
           | Default -> [])
         call.arguments)
  in
  let view_arguments =
    List.concat
      (List.mapi
         (fun position (argument : Mir.argument) ->
           match argument with
           | Passed { mode; value; _ } when is_view_operand builder value -> (
               let lent = find_lent_place builder mode value in
               match
                 ( find_operand_origin value,
                   List.filter
                     (fun view -> Some view <> Option.map (fun place -> Borrow_of place) lent)
                     (list_argument_views builder mode value) )
               with
               | Some _, [] | None, _ -> []
               | Some origin, views -> [ { position; views; origin } ])
           | Passed _ | Default -> [])
         call.arguments)
  in
  if List.length borrowed_arguments > 1 || (borrowed_arguments <> [] && view_arguments <> []) then
    emit builder (Arguments { borrowed_arguments; view_arguments; is_yielded = false }) origin;
  let can_store_in target (other : Mir.operand) =
    match find_operand_type other with
    | Some (Types.Function { output; _ }) when not (Context.is_view builder.context output) ->
        Context.holds_function builder.context target
    | _ -> true
  in
  List.iter
    (fun (argument : Mir.argument) ->
      match argument with
      | Passed { mode = Mut; value = target; _ } -> (
          match (find_lent_place builder Mut target, find_stored_type builder Mut target) with
          | Some place, Some stored_type when Context.is_view builder.context stored_type ->
              let others =
                List.filter
                  (fun (_, other) ->
                    other != target && is_view_operand builder other
                    && can_store_in stored_type other)
                  (list_viewable_arguments builder call)
              in
              emit builder
                (Store
                   {
                     place;
                     views =
                       List.concat_map
                         (fun (mode, other) -> list_argument_views builder mode other)
                         others;
                     replaces_root = false;
                   })
                origin
          | _ -> ())
      | _ -> ())
    call.arguments;
  List.iteri
    (fun position (argument : Mir.argument) ->
      match argument with
      | Passed { mode = Own; value = Use { type_ = Types.Function _; origin; _ } as value; _ }
        when Context.stores_function builder.context call.callee position ->
          emit builder (Pass_owned_function (list_argument_views builder Own value)) origin
      | _ -> ())
    call.arguments

let list_result_views builder (call : Mir.call) =
  List.concat_map
    (fun (mode, value) -> list_argument_views builder mode value)
    (list_viewable_arguments builder call)

let make_lent_part builder (call : Mir.call) ~part_type ~is_loop_part =
  let views =
    if Context.is_view builder.context part_type then list_result_views builder call
    else
      match call.arguments with
      | first :: _ -> (
          match find_viewable_argument builder first with
          | Some (mode, receiver) -> list_argument_views builder mode receiver
          | None -> [])
      | [] -> []
  in
  Lent_part { views; is_loop_part }

let compute_rvalue_held builder (value : Mir.rvalue) : held =
  match value with
  | Operand (Use { place = { root = Local local; projections } as place; _ })
    when (lookup_local_info builder local).kind = Temporary && not (Mir.is_in_sequence place) -> (
      match (Hashtbl.find_opt builder.held local, projections) with
      | Some (Value value), _ :: _ -> Value { value with lent = [] }
      | Some copied, _ -> copied
      | None, _ -> make_value [])
  | Operand operand -> make_value (list_operand_views builder operand)
  | Operation _ | Compare _ | Is_variant _ | Function_value _ | Value_parameter _ | Specification _
    ->
      make_value []
  | Not operand | Convert { value = operand; _ } | To_any { value = operand; _ } | Copy operand ->
      make_value (list_operand_views builder operand)
  | Construct { fields; _ } ->
      let supplied = List.filter_map snd fields in
      Value
        {
          views = List.concat_map (list_given_views builder) supplied;
          lent = List.concat_map (list_lent_places builder) supplied;
        }
  | Array elements -> make_value (List.concat_map (list_given_views builder) elements)
  | Lambda { captures = []; _ } -> make_value []
  | Lambda { captures; _ } ->
      make_value
        (Borrow_of { root = Environment; steps = [] }
        :: List.map
             (fun (capture : Mir.capture) -> Borrow_of { root = Local capture.local; steps = [] })
             captures)

let emit_bound_value builder (local : Mir.local) (core : Core.local) (value : Mir.rvalue) origin
    ~is_var =
  let type_ = (lookup_local_info builder local).type_ in
  let holds_views = Context.is_view builder.context type_ in
  let views =
    match value with
    | Operand (Borrow { place; type_ = part_type; origin = scrutinee; _ } as borrowed) ->
        let is_loop_part = is_loop_part builder place in
        (match find_untracked_lent_part builder place with
        | Some part
          when (not is_var) && (not is_loop_part)
               && ((not (Context.is_plain builder.context part_type))
                  || Context.is_view builder.context part_type) ->
            builder.lent_part_bindings <-
              { binding = local; part; origin; scrutinee } :: builder.lent_part_bindings
        | _ -> ());
        if
          holds_views || is_temporary builder place || is_loop_part
          || Option.is_some (track_place builder place)
             && not (Context.is_plain builder.context part_type)
        then list_operand_views builder borrowed
        else []
    | _ when holds_views -> list_held_views (compute_rvalue_held builder value)
    | _ -> []
  in
  let is_copy_of_loop_part =
    Context.is_plain builder.context type_
    &&
    match value with
    | Operand (Use { place; _ } | Borrow { place; _ }) -> is_loop_part builder place
    | _ -> false
  in
  let views =
    if is_copy_of_loop_part then
      List.map (fun view -> Copy_of_view_in (extract_viewed_place view)) views
    else views
  in
  if holds_views || views <> [] then emit builder (Bind_views { locals = [ core ]; views }) origin

let list_returned_temporaries (body : Mir.Graph.body) =
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
          (fun (statement : Mir.Graph.statement) ->
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

let list_loans builder (borrowed : Mir.operand) mode duration : loan list =
  List.map
    (fun view : loan -> { borrowed = extract_viewed_place view; mode; duration })
    (list_given_views builder borrowed)

let read_uses builder ?(is_returned = fun _ -> false) ?(skip = fun _ -> false) uses =
  List.iter
    (fun (use : Moves.use) ->
      if not (skip use) then evaluate builder ~is_returned:(is_returned use) use)
    uses

let emit_statement builder (statement : Mir.Graph.statement) =
  let origin = statement.origin in
  let uses = Moves.list_statement_uses builder.moves statement in
  match statement.kind with
  | Live locals ->
      builder.unassigned_locals <- locals @ builder.unassigned_locals;
      let core = List.filter_map (find_core_local builder) locals in
      if core <> [] then emit builder (Bind core) origin
  | Dead locals ->
      List.iter
        (fun (bound : lent_part_binding) ->
          if List.mem bound.part locals && not (List.mem bound.binding locals) then
            emit builder
              (Bind_lent_part
                 {
                   scrutinee = bound.scrutinee;
                   lent_part_type = (lookup_local_info builder bound.part).type_;
                 })
              bound.origin)
        builder.lent_part_bindings;
      let dropped =
        List.filter_map
          (fun local ->
            let info = lookup_local_info builder local in
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
         match (lookup_local_info builder local).kind with
         | Temporary -> true
         | Lent _ -> not (Hashtbl.mem builder.held local)
         | Source _ -> false -> (
      builder.unassigned_locals <-
        List.filter (fun unassigned -> unassigned <> local) builder.unassigned_locals;
      match (lookup_local_info builder local).kind with
      | Temporary -> (
          match value with
          | Operand (Use { place; _ })
            when List.mem local builder.returned_temporaries
                 && Option.is_some (track_place builder place) ->
              read_uses builder ~is_returned:(fun _ -> true) uses;
              hold builder target (make_value (list_copy_views builder place))
          | Operand (Borrow _) -> raise_bug "a temporary assigned a borrow"
          | _ ->
              read_uses builder uses;
              hold builder target (compute_rvalue_held builder value))
      | Lent _ -> (
          read_uses builder uses;
          match value with
          | Operand (Borrow { place; _ }) -> hold builder target (Alias place)
          | Convert { conversion = View_to_owned; _ } ->
              hold builder target (compute_rvalue_held builder value)
          | _ -> raise_bug "a lent local that holds neither a borrow nor the owner of a view")
      | Source { local = core; _ } ->
          read_uses builder uses;
          emit_bound_value builder local core value origin
            ~is_var:(List.mem core builder.context.mutable_locals))
  | Assign { target; value; _ } -> (
      read_uses builder uses;
      let target = resolve_alias builder target in
      let result = compute_rvalue_held builder value in
      match track_place builder target with
      | Some place -> (
          emit builder (Assign place) origin;
          match value with
          | Operand operand when is_view_operand builder operand ->
              emit builder
                (Store { place; views = list_held_views result; replaces_root = place.steps = [] })
                origin
          | _ -> ())
      | None -> hold builder { target with projections = [] } result)
  | Call { destination; call = called } ->
      read_uses builder uses;
      emit_call builder called origin;
      Option.iter
        (fun destination ->
          hold builder destination (make_value (list_result_views builder called)))
        destination
  | Template { destination; call = called; _ } ->
      read_uses builder uses;
      emit_call builder called origin;
      hold builder destination (make_value (list_result_views builder called))
  | Lend { part; call = called } ->
      read_uses builder uses;
      emit_call builder called origin;
      hold builder
        { Mir.root = Local part; projections = [] }
        (make_lent_part builder called ~part_type:(lookup_local_info builder part).type_
           ~is_loop_part:(List.mem part builder.loop_elements))
  | Assert _ | Echo _ -> read_uses builder uses
  | Provide { provided; _ } ->
      read_uses builder uses;
      List.iter
        (fun (provided : Mir.provided) ->
          if provided.mode = Mut then borrow_mut builder provided.value)
        provided
  | Loan_start { loan; borrowed; mode; duration } ->
      emit builder (Start_loan { loan; loans = list_loans builder borrowed mode duration }) origin;
      if duration = Loop_body then
        Hashtbl.replace builder.loop_body_starts builder.position.block (builder.position.index + 1)
  | Loan_end loans -> emit builder (End_loans loans) origin
  | Provide_end | Ghost_assert _ | Matched _ | Proof _ -> ()

let pull builder (iteration : Mir.iteration) origin =
  match iteration with
  | Pull { cursor; _ } ->
      Option.iter (fun tracked -> emit builder (Mutate tracked) origin) (track_place builder cursor)
  | Range _ -> ()

let emit_terminator builder ~returns_to_caller (basic : Mir.Graph.basic_block) =
  let origin = basic.terminator_origin in
  let uses = Moves.list_terminator_uses builder.moves basic in
  let return_value value =
    read_uses builder
      ~is_returned:(fun (use : Moves.use) ->
        match use.operand with
        | Some (Use { place; _ }) -> not (is_temporary builder place)
        | _ -> false)
      uses;
    match value with
    | Some value -> (
        match find_operand_type value with
        | Some type_ when returns_to_caller && Context.is_view builder.context type_ ->
            emit builder (Return_view (list_operand_views builder value)) origin
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
          hold builder part_place (make_value (list_copy_views builder cursor)))
  | Yield { mode; part; _ } ->
      let rec list_leaves : Mir.yielded -> Mir.operand list = function
        | Part operand -> [ operand ]
        | Built { fields; _ } ->
            List.concat_map (fun (_, field) -> Option.fold ~none:[] ~some:list_leaves field) fields
      in
      read_uses builder
        ~skip:(fun (use : Moves.use) ->
          match (part, use.operand) with
          | Part (Use { place = { root = Local local; projections = [] }; _ }), _ ->
              (lookup_local_info builder local).kind = Temporary
          | Built _, Some (Borrow _) -> true
          | _ -> false)
        uses;
      let lent = List.concat_map (list_lent_places builder) (list_leaves part) in
      if mode = Mut then begin
        List.iter (fun place -> emit builder (Mutate place) origin) lent;
        let borrowed_arguments =
          List.mapi (fun position place -> { place; mode; origin; position }) lent
        in
        if List.length borrowed_arguments > 1 then
          emit builder
            (Arguments { borrowed_arguments; view_arguments = []; is_yielded = true })
            origin
      end;
      let find_lent_by_address (operand : Mir.operand) =
        match (find_operand_place operand, find_operand_type operand) with
        | Some place, Some type_ when not (Context.is_plain builder.context type_) -> Some place
        | _ -> None
      in
      let parts =
        List.filter_map
          (fun leaf -> Option.bind (find_lent_by_address leaf) (track_place builder))
          (list_leaves part)
      in
      let forwarded =
        List.concat_map
          (fun (leaf : Mir.operand) ->
            match (find_lent_by_address leaf, find_operand_type leaf) with
            | Some place, Some type_
              when Option.is_some (find_untracked_lent_part builder place)
                   && not (Context.is_view builder.context type_) ->
                list_operand_views builder leaf
            | _ -> [])
          (list_leaves part)
      in
      let views =
        match part with
        | Part operand when is_view_operand builder operand -> list_operand_views builder operand
        | Part _ -> []
        | Built { type_; _ } when Context.is_view builder.context type_ ->
            List.concat_map (list_given_views builder) (list_leaves part)
        | Built _ -> []
      in
      emit builder (Yield_point { views; parts; forwarded }) origin
  | Return value -> return_value value
  | Cancel { returned; _ } -> return_value (Option.map fst returned)
  | Iteration_end { loop } ->
      pull builder (Mir.Graph.read_loop_head builder.body loop).iteration origin
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
      returned_temporaries = list_returned_temporaries body;
      loop_elements =
        Array.to_list body.blocks
        |> List.filter_map (fun (basic : Mir.Graph.basic_block) ->
            match basic.terminator with
            | For { elements = Some { element = Lent_by_call part; _ }; _ } -> Some part
            | _ -> None);
      loop_body_starts = Hashtbl.create 4;
      unassigned_locals = [];
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
        (fun index statement' ->
          write { block; index } (fun () -> emit_statement builder statement'))
        basic.statements;
      write
        { block; index = List.length basic.statements }
        (fun () -> emit_terminator builder ~returns_to_caller basic))
    body.blocks;
  let is_terminator { block; index } = index = List.length body.blocks.(block).statements in
  let list_positions ?(find_start = fun _ -> None) blocks =
    List.concat_map
      (fun block ->
        let first = Option.value ~default:0 (find_start block) in
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
                  List.map
                    (fun (branch : Mir.Graph.branch) -> list_positions branch.blocks)
                    branches;
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
                      || Mir.Graph.find_iteration_loop body.blocks.(position.block).terminator
                         <> Some loop_block)
                    (list_positions
                       ~find_start:(fun block ->
                         if block = inside then Hashtbl.find_opt builder.loop_body_starts inside
                         else None)
                       blocks);
                pattern_locals =
                  List.concat_map
                    (fun (statement : Mir.Graph.statement) ->
                      match statement.kind with
                      | Live locals -> List.filter_map (find_core_local builder) locals
                      | _ -> [])
                    body.blocks.(inside).statements;
                temporaries =
                  List.concat_map
                    (fun block ->
                      List.concat_map
                        (fun statement ->
                          List.filter_map
                            (fun (path : Moves.path) ->
                              if (lookup_local_info builder path.local).kind = Temporary then
                                Some path.local
                              else None)
                            (Moves.list_given_by statement))
                        body.blocks.(block).statements)
                    blocks;
              }
        | _ -> None)
  in
  { body; steps; fork_join_blocks; fork_join_loops }
