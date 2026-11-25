type entry = {
  evidence : (Path.t * Lowered.operand) list;
  provides : (Path.t * Lowered.operand) list list;
}

type region = {
  region_frame : Lowering.frame;
  region_body : Lowering.mir_frame;
  lowered : (Mir.Graph.block, Lowered.block) Hashtbl.t;
  mutable pending : (Mir.Graph.block * Lowered.block * entry) list;
  depth : int;
  start : entry;
  enclosing : region option;
  ending : (Core.id * Lowered.block) option;
}

let save (state : Lowering.state) =
  { evidence = state.evidence; provides = (Mir_places.require_mir_frame state).provides }

let make_region ?ending ?enclosing (state : Lowering.state) =
  {
    region_frame = state.frame;
    region_body = Mir_places.require_mir_frame state;
    lowered = Hashtbl.create 16;
    pending = [];
    depth = List.length state.scopes;
    start = save state;
    enclosing;
    ending;
  }

let restore (state : Lowering.state) (entry : entry) =
  state.evidence <- entry.evidence;
  (Mir_places.require_mir_frame state).provides <- entry.provides

let rec find_owner region body block =
  if region.region_body == body && Hashtbl.mem region.lowered block then Some region
  else Option.bind region.enclosing (fun enclosing -> find_owner enclosing body block)

let resolve_jump ?entry (state : Lowering.state) region target : Lowered.block =
  match find_owner region region.region_body target with
  | Some owner when owner == region -> Hashtbl.find region.lowered target
  | Some owner ->
      let pad = Emit_c.Ir_builder.allocate_block state.builder in
      let lowered = Hashtbl.find owner.lowered target in
      Emit_c.Ir_builder.run_in_block state.builder pad (fun () ->
          Lowering.leave_to state owner.depth;
          Emit_c.Ir_builder.finish state.builder (Goto lowered));
      pad
  | None ->
      let lowered = Emit_c.Ir_builder.allocate_block state.builder in
      Hashtbl.replace region.lowered target lowered;
      region.pending <-
        (target, lowered, Option.value entry ~default:(save state)) :: region.pending;
      lowered

let claim state region target = ignore (resolve_jump state region target)

let goto (state : Lowering.state) region target =
  Emit_c.Ir_builder.finish state.builder (Goto (resolve_jump state region target));
  Emit_c.Ir_builder.start state.builder (Emit_c.Ir_builder.allocate_block state.builder)

let continue_loop (state : Lowering.state) =
  match state.loops with
  | loop :: _ ->
      Lowering.leave_to state loop.continue_depth;
      Emit_c.Ir_builder.finish state.builder (Goto loop.continue_);
      Emit_c.Ir_builder.start state.builder (Emit_c.Ir_builder.allocate_block state.builder)
  | [] -> Definitions.raise_bug "the end of an iteration outside a loop"

let break_loop (state : Lowering.state) =
  match state.loops with
  | loop :: _ ->
      Lowering.leave_to state loop.break_depth;
      Emit_c.Ir_builder.finish state.builder (Goto loop.break_);
      Emit_c.Ir_builder.start state.builder (Emit_c.Ir_builder.allocate_block state.builder)
  | [] -> Definitions.raise_bug "a break outside a loop"

let lower_path_place state (path : Moves.path) =
  Mir_places.lower_place state { root = Local path.local; projections = path.projections }

let rec drop_path state (path : Moves.path) =
  let frame = Mir_places.require_mir_frame state in
  match Moves.find_status frame.moves frame.move_state path with
  | None -> (
      let place = lower_path_place state path in
      match Lowering.find_place_type state place with
      | Some (Value ty) when not (Lowering.is_trivial state ty) ->
          Emit_c.Ir_builder.emit state.builder (Drop place)
      | _ -> ())
  | Some Empty -> ()
  | Some Holds -> drop_held state path
  | Some Maybe ->
      let flag =
        match List.assoc_opt path frame.flags with
        | Some flag -> flag
        | None ->
            Definitions.raise_bug "local %d%s, which may hold nothing, has no flag" path.local
              (String.concat ""
                 (List.map
                    (function
                      | Mir.Field field -> "." ^ field
                      | Variant_field { variant; field } -> Printf.sprintf ".(%s).%s" variant field
                      | Element _ -> "[_]"
                      | Range _ -> "[_.._]")
                    path.projections))
      in
      Emit_c.Ir_builder.emit_when state.builder (Holds (Copy flag)) (fun () -> drop_held state path)

and drop_held state (path : Moves.path) =
  let frame = Mir_places.require_mir_frame state in
  if
    List.for_all
      (fun inner -> Moves.find_status frame.moves frame.move_state inner = Some Holds)
      (Moves.list_inside frame.moves path)
  then Emit_c.Ir_builder.emit state.builder (Drop (lower_path_place state path))
  else drop_parts state path

and drop_parts state (path : Moves.path) =
  let frame = Mir_places.require_mir_frame state in
  let place = lower_path_place state path in
  let ty =
    match Lowering.find_place_type state place with
    | Some (Value ty) -> ty
    | _ -> Definitions.raise_bug "a path to drop that holds no value"
  in
  let drop_child projection =
    let inner = { path with projections = path.projections @ [ projection ] } in
    match Lowering.find_place_type state (lower_path_place state inner) with
    | Some (Value inner_ty) when not (Lowering.is_trivial state inner_ty) -> drop_path state inner
    | _ -> ()
  in
  match (Memory_layout.of_type state.context.env ty).form with
  | Struct fields ->
      List.iter (fun (field : Memory_layout.field) -> drop_child (Field field.name)) fields
  | Tagged _ | Niche_encoded _ -> (
      let depth = List.length path.projections in
      let inside = Moves.list_inside frame.moves path in
      let variants =
        List.sort_uniq compare
          (List.filter_map
             (fun (inner : Moves.path) ->
               match List.nth_opt inner.projections depth with
               | Some (Variant_field { variant; _ }) -> Some variant
               | _ -> None)
             inside)
      in
      let open_variant variant =
        List.iter
          (fun (name, _) -> drop_child (Variant_field { variant; field = name }))
          (List.assoc (Some variant) (Mir_places.list_variants state ty));
        if Memory_layout.is_indirect state.context.env ty variant then
          Emit_c.Ir_builder.emit state.builder (Free_block { place; variant })
      in
      let is_certain variant =
        List.exists
          (fun (inner : Moves.path) ->
            match List.nth_opt inner.projections depth with
            | Some (Variant_field { variant = inner_variant; _ }) ->
                inner_variant = variant
                && Moves.find_status frame.moves frame.move_state inner = Some Empty
            | _ -> false)
          inside
      in
      match variants with
      | [] -> Emit_c.Ir_builder.emit state.builder (Drop place)
      | [ only ] when is_certain only -> open_variant only
      | variants ->
          let after = Emit_c.Ir_builder.allocate_block state.builder in
          let cases =
            List.map
              (fun variant ->
                let case = Emit_c.Ir_builder.allocate_block state.builder in
                Emit_c.Ir_builder.run_in_block state.builder case (fun () ->
                    open_variant variant;
                    Emit_c.Ir_builder.finish state.builder (Goto after));
                (variant, case))
              variants
          in
          let other = Emit_c.Ir_builder.allocate_block state.builder in
          Emit_c.Ir_builder.run_in_block state.builder other (fun () ->
              Emit_c.Ir_builder.emit state.builder (Drop place);
              Emit_c.Ir_builder.finish state.builder (Goto after));
          Emit_c.Ir_builder.finish state.builder
            (Switch_variant { place; cases; default = Some other });
          Emit_c.Ir_builder.start state.builder after)
  | _ -> Emit_c.Ir_builder.emit state.builder (Drop place)

let drop_local state local =
  let path : Moves.path = { local; projections = [] } in
  if
    Moves.owns (Mir_places.require_mir_frame state).moves local
    && Moves.find_status (Mir_places.require_mir_frame state).moves
         (Mir_places.require_mir_frame state).move_state path
       <> None
  then drop_path state path

let update_flags state ~before =
  let frame = Mir_places.require_mir_frame state in
  List.iter
    (fun ((path : Moves.path), holds) ->
      Emit_c.Ir_builder.emit state.builder
        (Assign (List.assoc path frame.flags, Use (Constant (Bool holds)))))
    (Moves.list_changed frame.moves ~before ~after:frame.move_state)

let drop_parameters state =
  List.iter (drop_local state) (Mir_places.require_mir_frame state).body.parameters

let drop_overwritten state (target : Mir.place) (destination : Lowered.place) ty =
  match Moves.find_place_path target with
  | Some path
    when (not (Mir.is_in_sequence target))
         && Moves.find_status (Mir_places.require_mir_frame state).moves
              (Mir_places.require_mir_frame state).move_state { path with projections = [] }
            <> None ->
      drop_path state path
  | _ ->
      if not (Lowering.is_trivial state ty) then
        Emit_c.Ir_builder.emit state.builder (Drop destination)

let return_from_frame (state : Lowering.state) =
  (match state.frame.exit with
  | Some (exit, depth) ->
      Lowering.leave_to state depth;
      Emit_c.Ir_builder.finish state.builder (Goto exit)
  | None ->
      drop_parameters state;
      Lowering.leave_to state 0;
      Emit_c.Ir_builder.finish state.builder (Lowering.return_result state));
  Emit_c.Ir_builder.start state.builder (Emit_c.Ir_builder.allocate_block state.builder)

let list_default_temporaries (default : Lowering.mir_frame) =
  List.filter
    (fun temporary ->
      (not (List.mem temporary default.returned))
      && Moves.owns default.moves temporary
      && Moves.find_status default.moves default.move_state { local = temporary; projections = [] }
         <> None)
    (List.init (Array.length default.body.locals) Fun.id)

let end_default_temporaries (state : Lowering.state) local =
  Option.iter
    (fun ({ default_frame; is_applied } : Lowering.applied_default) ->
      Emit_c.Ir_builder.emit_when state.builder (Holds (Copy is_applied)) (fun () ->
          let caller = state.frame in
          state.frame <- default_frame;
          List.iter (drop_local state)
            (list_default_temporaries (Mir_places.require_mir_frame state));
          state.frame <- caller;
          Emit_c.Ir_builder.emit state.builder (Assign (is_applied, Use (Constant (Bool false))))))
    (Hashtbl.find_opt (Mir_places.require_mir_frame state).applied_defaults local)

let end_local state local =
  let frame = Mir_places.require_mir_frame state in
  if List.mem local frame.called_parts && not (Hashtbl.mem frame.placed_parts local) then
    Mir_lends.emit_mark state
      (if frame.after_lend.(frame.block) then Lend_transfer else Lend_release)
      (Mir_lends.obtain_lent_call state local)
  else drop_local state local;
  end_default_temporaries state local
