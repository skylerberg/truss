let mir (st : Lowering.state) =
  match st.frame.mir with
  | Some mir -> mir
  | None -> Definitions.bug "MIR lowering outside a MIR frame"

let mir_of (context : Definitions.context) path : Mir.Graph.t =
  match Mir.graph_of_path context.lookups.mir path with
  | Some { form; _ } -> form
  | None -> Definitions.bug "%s has no MIR" (Path.show path)

let parameter_defaults (context : Definitions.context) path : (int * Mir.Graph.t) list Mir.sourced =
  match Mir.default_graphs_of_path context.lookups.mir path with
  | Some { source; form = Parameter_defaults defaults } -> { source; form = defaults }
  | Some { form = Field_defaults _; _ } | None ->
      Definitions.bug "%s is not a function" (Path.show path)

let parameter_of (body : Mir.Graph.body) local =
  match body.locals.(local) with
  | { kind = Source { mode; name; _ }; type_; _ } -> (mode, name, type_)
  | _ -> Definitions.bug "a parameter that is no source local"

let spans st = (Lowering.require_written st).spans

let site_of st (origin : Core.origin) =
  Lowering.site st (Source.Definition_span.locate (spans st) origin)

let reported_site (st : Lowering.state) : Lowered.operand option =
  match st.frame.mir with
  | Some { lending = Some { site; _ }; _ }
    when Path.package st.frame.code.definition = Path.standard_package ->
      Some site
  | _ -> None

let info st local = (mir st).body.locals.(local)

let core_local st local =
  match (info st local).kind with Source { local; _ } -> Some local | Temporary | Lent _ -> None

let bind_local st local place =
  Hashtbl.replace (mir st).places local place;
  if core_local st local = Some Self then st.frame.self_place <- Some place

let result_slot st =
  match (mir st).returns_into with
  | Some destination -> Some destination
  | None -> Lowering.result_place st

let rec fresh_place st local : Lowered.place =
  match result_slot st with
  | Some slot when List.mem local (mir st).returned ->
      bind_local st local slot;
      slot
  | _ -> new_place st local

and new_place st local : Lowered.place =
  let ty = Lowering.ground st (info st local).type_ in
  let name = match core_local st local with Some _ -> Some "binding" | None -> None in
  let place = Lowering.held st ?name (Value ty) in
  bind_local st local place;
  place

let local_place st local : Lowered.place =
  match Hashtbl.find_opt (mir st).places local with
  | Some place -> place
  | None -> fresh_place st local

let binary : Core.comparison -> Lowered.binary = function
  | Equal -> Equal
  | Not_equal -> Not_equal
  | Less -> Less
  | Less_equal -> Less_equal
  | Greater -> Greater
  | Greater_equal -> Greater_equal

let ground_argument (st : Lowering.state) argument =
  Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution argument

let split_arguments st type_arguments =
  let ground_arguments = List.map (ground_argument st) type_arguments in
  ( List.filter_map (function Ground.Type ty -> Some ty | _ -> None) ground_arguments,
    List.filter_map (function Ground.Value value -> Some value | _ -> None) ground_arguments )

let place st (written : Mir.place) : Lowered.place =
  let root =
    match written.root with
    | Local local -> local_place st local
    | Constant path -> Targets.static_constant st path
    | Literal { text; type_ } -> Targets.literal_place st (Lowering.ground st type_) text
  in
  List.fold_left
    (fun place (projection : Mir.projection) ->
      match projection with
      | Field field -> Lowered.project place (Field field)
      | Variant_field { variant; field } -> Lowered.project place (Variant_field { variant; field }))
    root written.projections

let variants_of (st : Lowering.state) (ty : Ground.ty) :
    (string option * (string * Ground.ty) list) list =
  let typed fields =
    List.map
      (fun (name, (member : Memory_layout.member)) ->
        match member with
        | Typed field_ty -> (name, field_ty)
        | Raw _ ->
            Definitions.bug "a field %s of %s that no Truss type names" name (Ground.to_string ty))
      fields
  in
  match Memory_layout.shape st.context.env ty with
  | Record fields -> [ (None, typed fields) ]
  | Sum variants ->
      List.map
        (fun (variant_shape : Memory_layout.variant_shape) ->
          (Some variant_shape.name, typed variant_shape.fields))
        variants
  | Scalar _ | Array _ -> Definitions.bug "the fields of %s, which has none" (Ground.to_string ty)

let frame_of_body (st : Lowering.state) ?owner ?returns_into ?lending
    ?(passed : Ground.mode list option) ~lambdas (body : Mir.Graph.body) : Lowering.mir_frame =
  let passed local : Types.mode option =
    Option.bind passed (fun modes ->
        Option.map
          (fun position : Types.mode ->
            match List.nth modes position with Ground.Read -> Read | Mut -> Mut | Own -> Own)
          (List.find_index (Int.equal local) body.parameters))
  in
  let needs_drop (path : Moves.path) =
    let rec path_type ty = function
      | [] -> Some ty
      | projection :: rest -> (
          let member =
            match (Memory_layout.shape st.context.env ty, (projection : Mir.projection)) with
            | Record fields, Field name -> List.assoc_opt name fields
            | Sum variants, Variant_field { variant; field } ->
                Option.bind
                  (List.find_opt
                     (fun (shape : Memory_layout.variant_shape) -> shape.name = variant)
                     variants)
                  (fun (shape : Memory_layout.variant_shape) -> List.assoc_opt field shape.fields)
            | _ -> None
          in
          match member with Some (Typed field_ty) -> path_type field_ty rest | _ -> None)
    in
    match path_type (Lowering.ground st body.locals.(path.local).type_) path.projections with
    | Some ty -> not (Lowering.is_trivial st ty)
    | None -> false
  in
  let moves = Moves.analyse ~passed ~tracks:needs_drop body in
  let after_lend = Array.make (Array.length body.blocks) false in
  let rec reach block =
    if not after_lend.(block) then begin
      after_lend.(block) <- true;
      List.iter reach (Mir.Graph.block_successors body block)
    end
  in
  Array.iter
    (fun (basic : Mir.Graph.basic_block) ->
      match basic.terminator with Yield { resume; _ } -> reach resume | _ -> ())
    body.blocks;
  let statements_where in_block select =
    List.concat
      (List.mapi
         (fun block (basic : Mir.Graph.basic_block) ->
           if in_block block then List.concat_map select basic.statements else [])
         (Array.to_list body.blocks))
  in
  {
    body;
    lambdas;
    places = Hashtbl.create 32;
    owner;
    returns_into;
    provides = [];
    returned =
      Array.fold_left
        (fun returned (block : Mir.Graph.basic_block) ->
          match block.terminator with
          | Return (Some (Use { place = { root = Local local; projections = [] }; _ }))
            when body.locals.(local).kind = Temporary ->
              local :: returned
          | _ -> returned)
        [] body.blocks;
    taken = [];
    moves;
    flags =
      List.map
        (fun (path : Moves.path) ->
          ( path,
            Lowered.make_local_place
              (Emit_c.Builder.local st.builder ~name:"owned" ~is_zeroed:true (Raw Bool)) ))
        (Moves.flagged moves);
    state = Moves.entry moves 0;
    lending;
    called_parts =
      statements_where
        (fun _ -> true)
        (fun (statement : Mir.Graph.statement) ->
          match statement.kind with
          | Lend { call = { callee = Intrinsic _; _ }; _ } -> []
          | Lend { part; _ } -> [ part ]
          | _ -> []);
    lent_calls = Hashtbl.create 4;
    placed_parts = Hashtbl.create 4;
    forwarded_locals = 0;
    ended_after_lend = statements_where (fun block -> after_lend.(block)) Moves.ended_by;
    after_lend;
    block = 0;
  }

let outlives_call ~(owns : Mir.local -> bool) ~(is_view : Types.ty -> bool) (body : Mir.Graph.body)
    (place : Mir.place) : bool =
  let operand_place (operand : Mir.operand) =
    match operand with
    | Borrow { place; type_; _ } | Use { place; type_; _ } | Take { place; type_; _ } ->
        Some (place, is_view type_)
    | Constant _ -> None
  in
  let viewed_by (call : Mir.call) =
    List.filter_map
      (function
        | Mir.Passed { mode; value; _ } -> (
            match operand_place value with
            | Some (place, holds_view) when holds_view || mode <> Own -> Some (place, holds_view)
            | _ -> None)
        | Default -> None)
      call.arguments
  in
  let receiver (call : Mir.call) =
    match call.arguments with
    | Passed { mode = Read | Mut; value; _ } :: _ -> Option.to_list (operand_place value)
    | _ -> []
  in
  let sources ~holds_view local : (Mir.place * bool) list option =
    let exception Made in
    let is_local (target : Mir.place) = target = { root = Local local; projections = [] } in
    let given (statement : Mir.Graph.statement) =
      match statement.kind with
      | Assign { target; value; _ } when is_local target -> (
          match value with
          | Operand (Borrow { place; _ }) -> [ (place, holds_view) ]
          | Operand ((Use _ | Take _) as operand) when holds_view ->
              Option.to_list (operand_place operand)
          | Construct { fields; _ } when holds_view ->
              List.filter_map
                (fun (_, field) ->
                  match (field : Mir.operand option) with
                  | Some (Borrow { place; _ }) -> Some (place, false)
                  | Some operand ->
                      Option.bind (operand_place operand) (fun (place, holds_view) ->
                          if holds_view then Some (place, true) else None)
                  | None -> None)
                fields
          | _ -> raise Made)
      | Lend { part; call } when part = local ->
          if holds_view then receiver call @ viewed_by call else receiver call
      | Slice { destination; base; call; _ } when is_local destination ->
          [ (base, match receiver call with (_, holds_view) :: _ -> holds_view | [] -> false) ]
      | (Call { destination = Some target; call } | Template { destination = target; call; _ })
        when is_local target ->
          if holds_view then viewed_by call else raise Made
      | _ -> []
    in
    try
      Some
        (Array.fold_left
           (fun places (block : Mir.Graph.basic_block) ->
             let places =
               List.fold_left
                 (fun places statement -> given statement @ places)
                 places block.statements
             in
             match block.terminator with
             | For { iteration = Pull { cursor; _ }; part; _ } when part = local && holds_view ->
                 (cursor, true) :: places
             | For { part; _ } when part = local -> raise Made
             | _ -> places)
           [] body.blocks)
    with Made -> None
  in
  let rec outlives seen ~holds_view (place : Mir.place) =
    match place.root with
    | Constant _ | Literal _ -> true
    | Local local when List.mem (local, holds_view) seen -> true
    | Local local -> (
        match body.locals.(local).kind with
        | Source { mode = Read | Mut; _ } when List.mem local body.parameters -> true
        | _ when List.mem local body.parameters -> holds_view
        | _ when owns local && not holds_view -> false
        | _ -> (
            match sources ~holds_view local with
            | Some places ->
                List.for_all
                  (fun (place, holds_view) ->
                    outlives ((local, holds_view) :: seen) ~holds_view place)
                  places
            | None -> false))
  in
  outlives [] ~holds_view:false place

let field_of variant field : Lowered.projection =
  match variant with Some variant -> Variant_field { variant; field } | None -> Field field

let owned_place st (written : Mir.place) =
  match written.root with
  | Literal { text; _ } -> Definitions.bug "the string literal %S used as an owned value" text
  | Local _ | Constant _ -> place st written

let taken st (written : Mir.place) =
  let frame = mir st in
  frame.taken <- written :: frame.taken;
  owned_place st written

let operand_type st operand = Lowering.ground st (Mir.operand_type operand)

let constant st ty (value : Mir.constant) : Lowered.operand =
  match value with
  | Unit -> Definitions.bug "a unit constant as a value"
  | Integer number -> Targets.constant_of st ty (Integer_value number)
  | Float number -> Targets.constant_of st ty (Float_value number)
  | Boolean truth -> Constant (Bool truth)

let value st (operand : Mir.operand) : Lowered.operand =
  let ty = operand_type st operand in
  match operand with
  | Constant { value; _ } -> constant st ty value
  | Use { place = written; _ } -> Lowering.owned st (owned_place st written) ty
  | Take { place = written; _ } -> Lowering.owned st (taken st written) ty
  | Borrow { place = written; _ } -> Copy (place st written)

let operand_place st (operand : Mir.operand) : Lowered.place =
  let ty = operand_type st operand in
  match operand with
  | Borrow { place = written; _ } -> place st written
  | Use { place = { root = Local local; projections = [] } as written; _ }
    when (info st local).kind = Temporary ->
      place st written
  | Use { place = written; _ } ->
      let held = Lowering.temporary st ty in
      Lowering.take st (owned_place st written) ty ~destination:held;
      held
  | Take { place = written; _ } ->
      let held = Lowering.temporary st ty in
      Lowering.take st (taken st written) ty ~destination:held;
      held
  | Constant { value = Unit; _ } -> Lowering.temporary st ty
  | Constant { value; _ } ->
      let held = Lowering.temporary st ty in
      Emit_c.Builder.emit st.builder (Assign (held, Use (constant st ty value)));
      held

let write_operand st (operand : Mir.operand) (destination : Lowered.place) =
  let ty = operand_type st operand in
  match operand with
  | Constant { value = Unit; _ } -> ()
  | Constant { value; _ } ->
      Emit_c.Builder.emit st.builder (Assign (destination, Use (constant st ty value)))
  | Use { place = written; _ } -> Lowering.take st (owned_place st written) ty ~destination
  | Take { place = written; _ } -> Lowering.take st (taken st written) ty ~destination
  | Borrow { place = written; _ } ->
      Emit_c.Builder.emit st.builder (Assign (destination, Use (Copy (place st written))))

let discarded st = Lowering.temporary st (Ground.builtin Unit)

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
  ending : (int * Lowered.block) option;
}

let save (st : Lowering.state) = { evidence = st.evidence; provides = (mir st).provides }

let new_region ?ending ?enclosing (st : Lowering.state) =
  {
    region_frame = st.frame;
    region_body = mir st;
    lowered = Hashtbl.create 16;
    pending = [];
    depth = List.length st.scopes;
    start = save st;
    enclosing;
    ending;
  }

let restore (st : Lowering.state) (entry : entry) =
  st.evidence <- entry.evidence;
  (mir st).provides <- entry.provides

let rec owner_of region body block =
  if region.region_body == body && Hashtbl.mem region.lowered block then Some region
  else Option.bind region.enclosing (fun enclosing -> owner_of enclosing body block)

let jump ?entry (st : Lowering.state) region target : Lowered.block =
  match owner_of region region.region_body target with
  | Some owner when owner == region -> Hashtbl.find region.lowered target
  | Some owner ->
      let pad = Emit_c.Builder.block st.builder in
      let lowered = Hashtbl.find owner.lowered target in
      Emit_c.Builder.in_block st.builder pad (fun () ->
          Lowering.leave_to st owner.depth;
          Emit_c.Builder.finish st.builder (Goto lowered));
      pad
  | None ->
      let lowered = Emit_c.Builder.block st.builder in
      Hashtbl.replace region.lowered target lowered;
      region.pending <- (target, lowered, Option.value entry ~default:(save st)) :: region.pending;
      lowered

let claim st region target = ignore (jump st region target)

let goto (st : Lowering.state) region target =
  Emit_c.Builder.finish st.builder (Goto (jump st region target));
  Emit_c.Builder.start st.builder (Emit_c.Builder.block st.builder)

let continue_loop (st : Lowering.state) =
  match st.loops with
  | loop :: _ ->
      Lowering.leave_to st loop.continue_depth;
      Emit_c.Builder.finish st.builder (Goto loop.continue_);
      Emit_c.Builder.start st.builder (Emit_c.Builder.block st.builder)
  | [] -> Definitions.bug "the end of an iteration outside a loop"

let break_loop (st : Lowering.state) =
  match st.loops with
  | loop :: _ ->
      Lowering.leave_to st loop.break_depth;
      Emit_c.Builder.finish st.builder (Goto loop.break_);
      Emit_c.Builder.start st.builder (Emit_c.Builder.block st.builder)
  | [] -> Definitions.bug "a break outside a loop"

let path_place st (path : Moves.path) =
  place st { root = Local path.local; projections = path.projections }

let rec drop_path st (path : Moves.path) =
  let frame = mir st in
  match Moves.status frame.moves frame.state path with
  | None -> (
      let place = path_place st path in
      match Lowering.place_type st place with
      | Some (Value ty) when not (Lowering.is_trivial st ty) ->
          Emit_c.Builder.emit st.builder (Drop place)
      | _ -> ())
  | Some Empty -> ()
  | Some Holds -> drop_held st path
  | Some Maybe ->
      let flag =
        match List.assoc_opt path frame.flags with
        | Some flag -> flag
        | None ->
            Definitions.bug "local %d%s, which may hold nothing, has no flag" path.local
              (String.concat ""
                 (List.map
                    (function
                      | Mir.Field field -> "." ^ field
                      | Variant_field { variant; field } -> Printf.sprintf ".(%s).%s" variant field)
                    path.projections))
      in
      Emit_c.Builder.when_ st.builder (Copy flag) (fun () -> drop_held st path)

and drop_held st (path : Moves.path) =
  let frame = mir st in
  if
    List.for_all
      (fun inner -> Moves.status frame.moves frame.state inner = Some Holds)
      (Moves.inside frame.moves path)
  then Emit_c.Builder.emit st.builder (Drop (path_place st path))
  else drop_parts st path

and drop_parts st (path : Moves.path) =
  let frame = mir st in
  let place = path_place st path in
  let ty =
    match Lowering.place_type st place with
    | Some (Value ty) -> ty
    | _ -> Definitions.bug "a path to drop that holds no value"
  in
  let child projection =
    let inner = { path with projections = path.projections @ [ projection ] } in
    match Lowering.place_type st (path_place st inner) with
    | Some (Value inner_ty) when not (Lowering.is_trivial st inner_ty) -> drop_path st inner
    | _ -> ()
  in
  match (Memory_layout.of_type st.context.env ty).form with
  | Struct fields ->
      List.iter (fun (field : Memory_layout.field) -> child (Field field.name)) fields
  | Tagged _ | Niche_encoded _ -> (
      let depth = List.length path.projections in
      let inside = Moves.inside frame.moves path in
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
          (fun (name, _) -> child (Variant_field { variant; field = name }))
          (List.assoc (Some variant) (variants_of st ty));
        if
          List.exists
            (fun (shape : Memory_layout.variant_shape) -> shape.name = variant && shape.indirect)
            (match Memory_layout.shape st.context.env ty with Sum shapes -> shapes | _ -> [])
        then Emit_c.Builder.emit st.builder (Free_block { place; variant })
      in
      let certain variant =
        List.exists
          (fun (inner : Moves.path) ->
            match List.nth_opt inner.projections depth with
            | Some (Variant_field { variant = inner_variant; _ }) ->
                inner_variant = variant && Moves.status frame.moves frame.state inner = Some Empty
            | _ -> false)
          inside
      in
      match variants with
      | [] -> Emit_c.Builder.emit st.builder (Drop place)
      | [ only ] when certain only -> open_variant only
      | variants ->
          let after = Emit_c.Builder.block st.builder in
          let cases =
            List.map
              (fun variant ->
                let case = Emit_c.Builder.block st.builder in
                Emit_c.Builder.in_block st.builder case (fun () ->
                    open_variant variant;
                    Emit_c.Builder.finish st.builder (Goto after));
                (variant, case))
              variants
          in
          let other = Emit_c.Builder.block st.builder in
          Emit_c.Builder.in_block st.builder other (fun () ->
              Emit_c.Builder.emit st.builder (Drop place);
              Emit_c.Builder.finish st.builder (Goto after));
          Emit_c.Builder.finish st.builder (Switch_variant { place; cases; default = Some other });
          Emit_c.Builder.start st.builder after)
  | _ -> Emit_c.Builder.emit st.builder (Drop place)

let drop_local st local =
  let path : Moves.path = { local; projections = [] } in
  if Moves.owns (mir st).moves local && Moves.status (mir st).moves (mir st).state path <> None then
    drop_path st path

let update_flags st ~before =
  let frame = mir st in
  List.iter
    (fun ((path : Moves.path), holds) ->
      Emit_c.Builder.emit st.builder
        (Assign (List.assoc path frame.flags, Use (Constant (Bool holds)))))
    (Moves.changed frame.moves ~before ~after:frame.state)

let drop_parameters st = List.iter (drop_local st) (mir st).body.parameters

let overwritten st (target : Mir.place) (destination : Lowered.place) ty =
  match Moves.path_of_place target with
  | Some path when Moves.status (mir st).moves (mir st).state { path with projections = [] } <> None
    ->
      drop_path st path
  | _ -> if not (Lowering.is_trivial st ty) then Emit_c.Builder.emit st.builder (Drop destination)

let return_from_frame (st : Lowering.state) =
  (match st.frame.exit with
  | Some (exit, depth) ->
      Lowering.leave_to st depth;
      Emit_c.Builder.finish st.builder (Goto exit)
  | None ->
      drop_parameters st;
      Lowering.leave_to st 0;
      Emit_c.Builder.finish st.builder (Lowering.return_result st));
  Emit_c.Builder.start st.builder (Emit_c.Builder.block st.builder)

let resolve_callee st (callee : Mir.callee) : (Path.t * Ground.argument list) option =
  match callee with
  | Function { path; type_arguments } -> Some (path, List.map (ground_argument st) type_arguments)
  | Trait_method { evidence = Dynamic; _ } -> None
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence } -> (
      match
        Targets.trait_method_key st.context st.frame.code.substitution ~trait ~name ~receiver
          ~self_type ~type_arguments ~evidence
      with
      | Code { path; type_arguments } -> Some (path, type_arguments)
      | _ -> Definitions.bug "a trait method's key")
  | Capability_method _ | Intrinsic _ | Indirect _ -> None

let resolved st (callee : Mir.callee) =
  match resolve_callee st callee with
  | Some (path, type_arguments) ->
      let signature = Definitions.signature_of st.context path in
      (path, type_arguments, signature, Definitions.bind signature.generics type_arguments)
  | None -> Definitions.bug "a callee that is not a function or a method"

let result_type st (callee : Mir.callee) =
  let path, _, signature, substitution = resolved st callee in
  match signature.output with
  | Returns ty -> Monomorphic.ground st.context.monomorphic substitution ty
  | Lends _ -> Definitions.bug "%s does not return a value" (Path.show path)

let call_with_places st (callee : Mir.callee) (places : Lowered.place list) ~destination =
  let path, type_arguments, signature, substitution = resolved st callee in
  let arguments =
    List.map2
      (fun (mode, ty) place ->
        (mode, Monomorphic.ground st.context.monomorphic substitution ty, place))
      (Definitions.interface_parameters signature)
      places
  in
  Targets.call_instance st
    (Code { path; type_arguments })
    ~signature ~substitution ~arguments ~destination ()

let evaluate_arguments (st : Lowering.state) (signature : Types.signature) substitution
    (arguments : Mir.argument list) =
  let parameters = Definitions.interface_parameters signature in
  if List.length parameters <> List.length arguments then
    Definitions.bug "a call with %d arguments for %d parameters" (List.length arguments)
      (List.length parameters);
  let receivers = List.length parameters - List.length signature.parameters in
  let mask = ref 0 and defaulted = ref 0 in
  let evaluated =
    List.mapi
      (fun index ((mode, ty), (argument : Mir.argument)) ->
        let ty = Monomorphic.ground st.context.monomorphic substitution ty in
        let bit =
          if index >= receivers && (List.nth signature.parameters (index - receivers)).has_default
          then begin
            incr defaulted;
            Some (!defaulted - 1)
          end
          else None
        in
        match argument with
        | Default ->
            ( mode,
              ty,
              Lowered.make_local_place (Emit_c.Builder.local st.builder ~is_zeroed:true (Value ty))
            )
        | Passed { value; _ } ->
            Option.iter (fun bit -> mask := !mask lor (1 lsl bit)) bit;
            (mode, ty, operand_place st value))
      (List.combine parameters arguments)
  in
  if !defaulted > 62 then
    Lowering.unsupported "a function with more than 62 parameters that have defaults";
  (evaluated, !mask)

let argument_place st (argument : Mir.argument) =
  match argument with
  | Passed { mode; value; _ } -> (mode, operand_type st value, operand_place st value)
  | Default -> Definitions.bug "an omitted argument in a call that has no defaults"

let shared_update st ~shared ~input ~change ~destination =
  let _, _, shared = argument_place st shared in
  let _, _, input = argument_place st input in
  let _, change_ty, change = argument_place st change in
  let function_type =
    match change_ty with
    | Function function_type -> function_type
    | ty -> Definitions.bug "shared_update with a %s, which is not a function" (Ground.to_string ty)
  in
  let value_ty, result_ty =
    match function_type.parameters with
    | (_, value_ty) :: _ -> (value_ty, function_type.result)
    | [] -> Definitions.bug "shared_update with a function that takes no value"
  in
  let pointer = Lowered.Copy (Lowered.project shared (Field "value")) in
  Emit_c.Builder.emit st.builder
    (Call { target = Intrinsic Shared_lock; arguments = [ pointer ]; result = Discarded });
  let typed =
    Emit_c.Builder.local st.builder (Pointer { target = Value value_ty; writable = true })
  in
  Emit_c.Builder.emit st.builder (Assign (Lowered.make_local_place typed, Use pointer));
  let result =
    match destination with
    | Some destination -> destination
    | None -> Lowering.temporary st result_ty
  in
  Targets.call_indirect st ~function_type ~value:change
    [ { root = Local typed; projections = [ Deref ] }; input ]
    result;
  Emit_c.Builder.emit st.builder
    (Call { target = Intrinsic Shared_unlock; arguments = [ pointer ]; result = Discarded })

let intrinsic st ?reported (operation : Intrinsic.operation) ~type_arguments
    (arguments : Mir.argument list) ~destination ~site =
  match (operation, arguments) with
  | Shared_update, [ shared; input; change ] ->
      shared_update st ~shared ~input ~change ~destination;
      None
  | _ ->
      let type_arguments, value_arguments = split_arguments st type_arguments in
      let arguments =
        List.map
          (fun (argument : Mir.argument) ->
            match argument with
            | Passed { value = Borrow _ as borrowed; _ } ->
                Intrinsics.Place (operand_place st borrowed)
            | Passed { value = passed; _ } ->
                let ty = operand_type st passed in
                if Storage.match_storage_element ty <> None || Storage.match_view_element ty <> None
                then Intrinsics.Place (operand_place st passed)
                else Intrinsics.Value (value st passed)
            | Default -> Definitions.bug "an intrinsic called with an omitted argument")
          arguments
      in
      List.iter
        (fun position ->
          match List.nth arguments position with
          | Intrinsics.Place place -> ignore (Lowering.moved st place)
          | Value _ -> ())
        (Intrinsics.consumed_places operation);
      Intrinsics.lower ~checks:st.context.checks ~value_arguments ?reported st.context.env
        st.builder st.context.types operation ~type_arguments arguments ~destination ~site

let field_default (st : Lowering.state) (ty : Ground.ty) ~variant ~field :
    Mir.Graph.t Mir.field_default Mir.sourced =
  let path =
    match ty with
    | Named { path; _ } -> path
    | _ -> Definitions.bug "defaults of %s" (Ground.to_string ty)
  in
  match Mir.default_graphs_of_path st.context.lookups.mir path with
  | Some { source; form = Field_defaults defaults } -> (
      match
        List.find_opt
          (fun (default : Mir.Graph.t Mir.field_default) ->
            default.variant = variant && default.field = field)
          defaults
      with
      | Some default -> { source; form = default }
      | None -> Definitions.bug "%s has no default for %s" (Path.show path) field)
  | Some { form = Parameter_defaults _; _ } | None ->
      Definitions.bug "%s is not a type" (Path.show path)

let tasks_call (st : Lowering.state) name ?result (places : Lowered.place list) : Lowered.statement
    =
  let capability = Well_known.path Tasks in
  let slot, signature = Targets.capability_method st.context capability name in
  let c_signature, convention = Targets.entry_signature st.context signature in
  Call
    {
      target =
        Evidence_call
          {
            evidence = Targets.evidence_of st capability;
            capability;
            slot;
            signature = c_signature;
          };
      arguments =
        List.filter_map Fun.id
          (List.map2
             (fun (mode, ty) place ->
               Targets.pass st mode (Monomorphic.ground st.context.monomorphic [] ty) place)
             (Definitions.interface_parameters { signature with receiver = None })
             places);
      result =
        (match result with
        | Some place -> Convention.destination convention place
        | None -> Discarded);
    }

let tasks_bool (st : Lowering.state) name places : Lowered.operand =
  let result = Lowered.make_local_place (Emit_c.Builder.local st.builder (Value st.context.bool)) in
  Emit_c.Builder.emit st.builder (tasks_call st name ~result places);
  Copy result

let with_group st (f : Lowered.place -> unit) =
  let scope = Lowering.open_scope st Statement in
  let group =
    Lowered.make_local_place
      (Emit_c.Builder.local st.builder ~name:"group" (Value (Ground.builtin UInt64)))
  in
  Emit_c.Builder.emit st.builder (tasks_call st "open" ~result:group []);
  let join = tasks_call st "join" [ group ] in
  let cleanup = Lowering.Join_group join in
  scope.owned <- [ cleanup ];
  f group;
  Emit_c.Builder.emit st.builder join;
  scope.owned <- List.filter (fun owned -> owned != cleanup) scope.owned;
  Lowering.close_scope st scope

let task_function_type (st : Lowering.state) : Lowered.ty =
  let _, signature = Targets.capability_method st.context (Well_known.path Tasks) "spawn" in
  match signature.parameters with
  | [ _; work; _ ] -> Value (Monomorphic.ground st.context.monomorphic [] work.type_)
  | _ -> Definitions.bug "Tasks.spawn does not take a group, a function, and an item"

let task_body st ~(id : Mir.task) ~group ~parts (f : Lowering.task -> unit) : Lowered.rvalue =
  let nested, environment =
    Lowering.outlined st ~parts (fun () ->
        let task =
          {
            Lowering.id;
            group;
            end_block = Emit_c.Builder.block st.builder;
            scope_depth = List.length st.scopes;
          }
        in
        st.tasks <- task :: st.tasks;
        f task;
        st.tasks <- List.tl st.tasks;
        Emit_c.Builder.finish st.builder (Goto task.end_block);
        Emit_c.Builder.start st.builder task.end_block;
        Emit_c.Builder.finish st.builder (Return None))
  in
  Function_value { code = Nested nested; environment = Some environment }

let locked_evidence (st : Lowering.state) ~(tasks : Lowered.operand)
    (evidence : (Path.t * Lowered.operand) list) =
  let mutex =
    Lowered.make_local_place
      (Emit_c.Builder.local st.builder ~name:"mutex" (Value (Ground.builtin UInt64)))
  in
  Emit_c.Builder.emit st.builder (Assign (mutex, Use (Lowering.constant_int UInt64 Z.zero)));
  List.map
    (fun (capability, implementation) ->
      let slot = Emit_c.Builder.local st.builder (Evidence 2) in
      Emit_c.Builder.emit st.builder
        (Call
           {
             target = Intrinsic Evidence_fill;
             arguments =
               [
                 Address { place = Lowered.make_local_place slot; writable = true };
                 Address { place = mutex; writable = true };
                 Constant (Symbol_address (Table (Locked_table capability)));
                 implementation;
                 tasks;
               ];
             result = Discarded;
           });
      (capability, Lowered.Address { place = Lowered.make_local_place slot; writable = false }))
    evidence

let cancel (st : Lowering.state) ~(task : Mir.task) ~winner ~number ~value =
  match st.tasks with
  | current :: _ when current.id = task ->
      let won = Emit_c.Builder.block st.builder
      and lost = Emit_c.Builder.block st.builder
      and after = Emit_c.Builder.block st.builder in
      Emit_c.Builder.branch st.builder (tasks_bool st "cancel" [ current.group ]) ~yes:won ~no:lost;
      Emit_c.Builder.start st.builder won;
      Emit_c.Builder.emit st.builder
        (Assign (local_place st winner, Use (Lowering.constant_int UInt32 (Z.of_int number))));
      Option.iter
        (fun (value, ty, slot) ->
          Emit_c.Builder.emit st.builder
            (Assign (local_place st slot, Use (Lowering.owned st value ty))))
        value;
      Emit_c.Builder.finish st.builder (Goto after);
      Emit_c.Builder.start st.builder lost;
      Option.iter
        (fun (value, ty, _) ->
          if not (Lowering.is_trivial st ty) then Emit_c.Builder.emit st.builder (Drop value))
        value;
      Emit_c.Builder.finish st.builder (Goto after);
      Emit_c.Builder.start st.builder after;
      Lowering.leave_to st current.scope_depth;
      Emit_c.Builder.finish st.builder (Goto current.end_block);
      Emit_c.Builder.start st.builder (Emit_c.Builder.block st.builder)
  | _ -> Definitions.bug "an early exit leaves a task that is not the innermost enclosing task"

let spawn_iteration (st : Lowering.state) (loop : Lowering.spawn_loop) ~(not_spawned : unit -> unit)
    (f : unit -> unit) =
  let function_value = Emit_c.Builder.local st.builder ~name:"task" (task_function_type st) in
  Emit_c.Builder.emit st.builder
    (Assign
       ( Lowered.make_local_place function_value,
         task_body st
           ~id:(Iteration { loop = loop.origin })
           ~group:loop.group ~parts:[ loop.item ]
           (fun task ->
             Lowering.looping st ~continue_:task.end_block ~break_:task.end_block
               ~depth:task.scope_depth f) ));
  let spawned =
    tasks_bool st "spawn"
      [ loop.group; Lowered.make_local_place function_value; Lowered.make_local_place loop.item ]
  in
  let next = Emit_c.Builder.block st.builder and cancelled = Emit_c.Builder.block st.builder in
  Emit_c.Builder.branch st.builder spawned ~yes:next ~no:cancelled;
  Emit_c.Builder.start st.builder cancelled;
  not_spawned ();
  break_loop st;
  Emit_c.Builder.start st.builder next

let spawn_with_item st (loop : Lowering.spawn_loop) (value : Lowered.place) ~owned:is_owned
    ~(each : Lowered.place -> unit) =
  let ty = loop.element in
  let item = Lowered.make_local_place loop.item in
  let boxed = not (Lowering.is_zero_size st ty) in
  let move_or_copy place : Lowered.operand =
    if is_owned then Lowering.owned st place ty else Copy place
  in
  let block_of () : Lowered.local * Lowered.place =
    let pointer = Emit_c.Builder.local st.builder (Raw (Pointer Opaque)) in
    Emit_c.Builder.emit st.builder
      (Assign (Lowered.make_local_place pointer, Convert (Copy item, Pointer Opaque)));
    let typed = Emit_c.Builder.local st.builder (Pointer { target = Value ty; writable = true }) in
    Emit_c.Builder.emit st.builder
      (Assign (Lowered.make_local_place typed, Use (Copy (Lowered.make_local_place pointer))));
    (pointer, { root = Local typed; projections = [ Deref ] })
  in
  let unbox ~dropped_here : Lowered.place =
    if boxed then begin
      let unboxed =
        if is_owned && dropped_here then Lowering.binding st ty
        else Lowered.make_local_place (Emit_c.Builder.local st.builder (Value ty))
      in
      let pointer, inside = block_of () in
      Emit_c.Builder.emit st.builder (Assign (unboxed, Use (move_or_copy inside)));
      Emit_c.Builder.emit st.builder
        (Call
           {
             target = Intrinsic Free;
             arguments = [ Copy (Lowered.make_local_place pointer) ];
             result = Discarded;
           });
      unboxed
    end
    else Lowered.make_local_place (Emit_c.Builder.local st.builder (Value ty))
  in
  if boxed then begin
    let pointer = Emit_c.Builder.local st.builder (Raw (Pointer Opaque)) in
    Emit_c.Builder.emit st.builder
      (Call
         {
           target = Intrinsic Allocate;
           arguments = [ Constant (Size_of ty); Constant (Alignment_of ty) ];
           result = Returned (Lowered.make_local_place pointer);
         });
    Emit_c.Builder.emit st.builder
      (Assign (item, Convert (Copy (Lowered.make_local_place pointer), Integer UInt64)));
    Emit_c.Builder.emit st.builder (Assign (snd (block_of ()), Use (move_or_copy value)))
  end
  else Emit_c.Builder.emit st.builder (Assign (item, Use (Lowering.constant_int UInt64 Z.zero)));
  spawn_iteration st loop
    ~not_spawned:(fun () -> Lowering.in_scope st (fun () -> ignore (unbox ~dropped_here:true)))
    (fun () -> Lowering.in_scope st (fun () -> each (unbox ~dropped_here:false)))

let lend_record (st : Lowering.state) : Lowered.operand =
  match st.lend_record with
  | Some record -> record
  | None ->
      let record : Lowered.operand =
        Address
          {
            place =
              Lowered.make_local_place
                (Emit_c.Builder.local st.builder ~name:"lend" ~is_zeroed:true Lend);
            writable = true;
          }
      in
      st.lend_record <- Some record;
      record

let lent_call st part : Lowering.lent_call =
  let frame = mir st in
  match Hashtbl.find_opt frame.lent_calls part with
  | Some call -> call
  | None ->
      let call =
        {
          Lowering.mark =
            Lowered.make_local_place
              (Emit_c.Builder.local st.builder ~name:"lent" ~is_zeroed:true Lend_mark);
          record = lend_record st;
        }
      in
      Hashtbl.replace frame.lent_calls part call;
      call

let emit_mark (st : Lowering.state) (intrinsic : Lowered.intrinsic) (call : Lowering.lent_call) =
  Emit_c.Builder.emit st.builder
    (Call
       {
         target = Intrinsic intrinsic;
         arguments = [ call.record; Address { place = call.mark; writable = true } ];
         result = Discarded;
       })

let forwarded_call st (call : Mir.call) : Forwarded.t option =
  match resolve_callee st call.callee with
  | Some (path, type_arguments) when Path.package path = Path.standard_package ->
      let frame = mir st in
      let fresh () =
        frame.forwarded_locals <- frame.forwarded_locals + 1;
        -frame.forwarded_locals
      in
      let code = Definitions.code_of st.context path type_arguments in
      Option.bind
        (Forwarded.call ~substitution:code.substitution ~fresh (mir_of st.context path) call)
        (fun (forwarded : Forwarded.t) ->
          if
            List.for_all
              (fun (_, type_, _) -> Lowering.is_trivial st (Lowering.ground st type_))
              forwarded.setup
          then Some forwarded
          else None)
  | _ -> None

let is_forwarded_whole (frame : Lowering.mir_frame) part =
  match frame.body.blocks.(frame.block).terminator with
  | Yield { part = Part (Borrow { place = { root = Local lent; projections = [] }; _ }); _ } ->
      lent = part
  | _ -> false

type deferred =
  | Deferred_drop of Ground.ty
  | Deferred_write_back of { source : Lowered.place; ty : Ground.ty }
  | Deferred_free of string

let make_owned_locals st =
  let frame = mir st in
  let parts =
    Array.fold_left
      (fun parts (block : Mir.Graph.basic_block) ->
        match block.terminator with For { part; _ } -> part :: parts | _ -> parts)
      [] frame.body.blocks
  in
  Array.iteri
    (fun local _ ->
      if
        Moves.owns frame.moves local
        && (not (List.mem local frame.body.parameters))
        && not (List.mem local parts)
      then ignore (local_place st local))
    frame.body.locals

let rec lower_body (st : Lowering.state) (frame : Lowering.mir_frame) =
  st.frame <- { st.frame with mir = Some frame };
  List.iter
    (fun path ->
      Emit_c.Builder.emit st.builder
        (Assign (List.assoc path frame.flags, Use (Constant (Bool true)))))
    (Moves.held_at_entry frame.moves);
  run_region st (new_region st) ~entry:(0, 0)

and run_region st region ~entry:(block, index) =
  let caller = st.frame in
  st.frame <- region.region_frame;
  lower_from st region block index;
  let rec drain () =
    match
      List.fold_left
        (fun first ((block, _, _) as next) ->
          match first with Some (earliest, _, _) when earliest <= block -> first | _ -> Some next)
        None region.pending
    with
    | None -> ()
    | Some (next, lowered, entry) ->
        region.pending <- List.filter (fun (block, _, _) -> block <> next) region.pending;
        restore st entry;
        Emit_c.Builder.in_block st.builder lowered (fun () ->
            lower_from st region next 0;
            Emit_c.Builder.finish st.builder Unreachable);
        drain ()
  in
  drain ();
  st.frame <- caller

and lower_from st region block index =
  let basic = (mir st).body.blocks.(block) in
  st.frame <- region.region_frame;
  let frame = mir st in
  frame.block <- block;
  frame.state <- Moves.entry frame.moves block;
  if index = 0 then
    List.iter
      (fun path ->
        Emit_c.Builder.emit st.builder
          (Assign (List.assoc path frame.flags, Use (Constant (Bool true)))))
      (Moves.given_on_entry frame.moves block);
  List.iteri
    (fun position (statement : Mir.Graph.statement) ->
      if position >= index then begin
        let before = Moves.copy frame.state in
        Moves.apply_moves frame.moves frame.state statement;
        Lowering.in_statement st (fun () -> lower_statement st statement);
        Moves.apply frame.moves frame.state statement;
        update_flags st ~before
      end
      else Moves.apply frame.moves frame.state statement)
    basic.statements;
  let before = Moves.copy frame.state in
  Moves.apply_terminator_moves frame.moves frame.state basic;
  update_flags st ~before;
  terminator st region basic.terminator ~origin:basic.terminator_origin

and concurrent_block st region ~fork ~(branches : Mir.Graph.branch list) ~join =
  let function_type = task_function_type st in
  let item = Emit_c.Builder.local st.builder (Value (Ground.builtin UInt64)) in
  Emit_c.Builder.emit st.builder
    (Assign (Lowered.make_local_place item, Use (Lowering.constant_int UInt64 Z.zero)));
  with_group st (fun group ->
      let functions =
        List.mapi
          (fun index (branch : Mir.Graph.branch) ->
            task_body st
              ~id:(Branch { block = fork; index })
              ~group ~parts:[ item ]
              (fun task ->
                let inner = new_region st ~enclosing:region ~ending:(fork, task.end_block) in
                run_region st inner ~entry:(branch.entry, 0)))
          branches
      in
      List.iter
        (fun code ->
          let function_value =
            Lowered.make_local_place (Emit_c.Builder.local st.builder ~name:"task" function_type)
          in
          Emit_c.Builder.emit st.builder (Assign (function_value, code));
          ignore (tasks_bool st "spawn" [ group; function_value; Lowered.make_local_place item ]))
        functions);
  match join with Some join -> goto st region join | None -> Lowering.unreachable_block st

and lower_statement st (statement : Mir.Graph.statement) =
  let origin = statement.origin in
  match statement.kind with
  | Assign { target; value; _ } -> assign st target value ~origin
  | Call { destination; call } ->
      let destination =
        match destination with
        | Some written ->
            let destination = place st written in
            (match Lowering.place_type st destination with
            | Some (Value ty) -> overwritten st written destination ty
            | _ -> ());
            destination
        | None -> discarded st
      in
      call_into st call destination ~origin
  | Lend { part; call } -> lend st part call ~origin
  | Slice { destination; call; _ } | Template { destination; call; _ } ->
      call_into st call (place st destination) ~origin
  | Live _ | Loan_start _ | Loan_end _ | Ghost_assert _ | Matched _ | Proof _ -> ()
  | Dead locals -> List.iter (dead st) locals
  | Assert condition ->
      let holds = value st condition in
      let failed = Emit_c.Builder.block st.builder and after = Emit_c.Builder.block st.builder in
      Emit_c.Builder.branch st.builder holds ~yes:after ~no:failed;
      Emit_c.Builder.start st.builder failed;
      let text =
        match condition with
        | Constant { value = Boolean truth; _ } -> string_of_bool truth
        | Use { origin; _ } | Borrow { origin; _ } | Take { origin; _ } ->
            Lowering.source st (spans st).(origin)
        | Constant _ -> Lowering.source st (spans st).(origin)
      in
      let message = "assert " ^ text in
      Emit_c.Builder.finish st.builder
        (Fail
           {
             failure = Assertion;
             message = Constant (Bytes message);
             length = Lowered.make_uint64_constant (String.length message);
             site = site_of st origin;
             reported = None;
           });
      Emit_c.Builder.start st.builder after
  | Echo echoed ->
      Targets.echo st (operand_place st echoed) (operand_type st echoed) ~site:(site_of st origin)
  | Provide { provided; can_use_tasks } -> provide st provided ~can_use_tasks
  | Provide_end -> (
      let frame = mir st in
      match frame.provides with
      | enclosing :: rest ->
          st.evidence <- enclosing;
          frame.provides <- rest
      | [] -> Definitions.bug "the end of a provide that did not start")

and dead st local =
  let frame = mir st in
  if List.mem local frame.called_parts && not (Hashtbl.mem frame.placed_parts local) then
    emit_mark st
      (if frame.after_lend.(frame.block) then Lend_transfer else Lend_release)
      (lent_call st local)
  else drop_local st local

and provide st (provided : Mir.provided list) ~can_use_tasks =
  let enclosing = st.evidence in
  let implementations =
    List.map
      (fun (implementation : Mir.provided) ->
        let place =
          match implementation.value with
          | Use { place = written; _ } | Borrow { place = written; _ } -> place st written
          | value -> operand_place st value
        in
        let pointer =
          if Lowering.is_zero_size st (Lowering.ground st implementation.type_) then
            Lowered.Constant Null
          else Address { place; writable = true }
        in
        ( implementation.mode,
          Targets.provided_evidence st ~implementation:pointer
            (List.map
               (fun (provided : Core.provided) ->
                 (provided.capability, provided.impl, provided.arguments))
               implementation.provides) ))
      provided
  in
  let is_tasks (capability, _) = Path.equal capability (Well_known.path Tasks) in
  let tasks =
    if can_use_tasks then
      Option.map snd (List.find_opt is_tasks (List.concat_map snd implementations @ enclosing))
    else None
  in
  let added =
    List.concat_map
      (fun ((mode : Types.mode), evidence) ->
        match tasks with
        | Some tasks when mode = Mut && not (List.exists is_tasks evidence) ->
            locked_evidence st ~tasks evidence
        | _ -> evidence)
      implementations
  in
  let frame = mir st in
  frame.provides <- enclosing :: frame.provides;
  st.evidence <- added @ enclosing

and target_type st (target : Mir.place) (value : Mir.rvalue) =
  match (target, value) with
  | _, Operand operand -> operand_type st operand
  | _ -> mir_place_type st target

and mir_place_type st (written : Mir.place) =
  match written with
  | { root = Local local; projections = [] } -> Lowering.ground st (info st local).type_
  | _ -> (
      match Lowering.place_type st (place st written) with
      | Some (Value ty) -> ty
      | _ -> Definitions.bug "a place of no known type")

and assign st (target : Mir.place) (value : Mir.rvalue) ~origin =
  match (target, value) with
  | { root = Local local; projections = [] }, Operand (Borrow { place = source; mode; _ }) ->
      alias st local (place st source) ~writable:(mode = Mut)
  | _ -> (
      let ty = target_type st target value in
      let types_ty =
        match target with
        | { root = Local local; projections = [] } -> Some (info st local).type_
        | _ -> None
      in
      let reads_target =
        match target.root with Local local -> reads value local | Constant _ | Literal _ -> false
      in
      let evaluated =
        if reads_target then begin
          let fresh = Lowering.temporary st ty in
          into ?types_ty st value fresh ty ~origin;
          Some fresh
        end
        else None
      in
      let destination = place st target in
      let frame = mir st in
      if List.mem target frame.taken then
        frame.taken <- List.filter (fun taken -> taken <> target) frame.taken
      else overwritten st target destination ty;
      match evaluated with
      | Some fresh ->
          Emit_c.Builder.emit st.builder (Assign (destination, Use (Lowering.owned st fresh ty)))
      | None -> into ?types_ty st value destination ty ~origin)

and reads (value : Mir.rvalue) local =
  let in_place (written : Mir.place) = written.root = Local local in
  let in_operand (operand : Mir.operand) =
    match operand with
    | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> in_place place
    | Constant _ -> false
  in
  match value with
  | Operand operand | Not operand | Copy operand -> in_operand operand
  | Convert { value; _ } | To_any { value; _ } -> in_operand value
  | Operation { operands; _ } | Array operands -> List.exists in_operand operands
  | Compare { left; right; _ } -> in_operand left || in_operand right
  | Construct { fields; _ } ->
      List.exists (fun (_, field) -> Option.fold ~none:false ~some:in_operand field) fields
  | Is_variant { place; _ } -> in_place place
  | Function_value _ | Lambda _ | Value_parameter _ | Specification _ -> false

and alias st local (source : Lowered.place) ~writable =
  let ty = Lowering.ground st (info st local).type_ in
  if (info st local).has_several_bindings then begin
    let frame = mir st in
    let pointer =
      match Hashtbl.find_opt frame.places local with
      | Some { root = Local pointer; projections = [ Deref ] } -> Lowered.make_local_place pointer
      | Some { root = Local pointer; projections = [ Deref; Field field; Deref ] } ->
          { root = Local pointer; projections = [ Deref; Field field ] }
      | _ ->
          let pointer =
            Lowering.held st ~name:"binding" (Pointer { target = Value ty; writable })
          in
          bind_local st local (Lowered.project pointer Deref);
          pointer
    in
    Emit_c.Builder.emit st.builder (Assign (pointer, Use (Address { place = source; writable })))
  end
  else if
    (not writable)
    && (match (Memory_layout.of_type st.context.env ty).form with Scalar _ -> true | _ -> false)
    && match (info st local).kind with Source _ -> true | Temporary | Lent _ -> false
  then begin
    let copy = Lowering.held st ~name:"binding" (Value ty) in
    Emit_c.Builder.emit st.builder (Assign (copy, Use (Copy source)));
    bind_local st local copy
  end
  else bind_local st local (Lowering.snapshot st source)

and into ?types_ty st (rvalue : Mir.rvalue) (destination : Lowered.place) ty ~origin =
  let assign built = Emit_c.Builder.emit st.builder (Assign (destination, built)) in
  match rvalue with
  | Operand operand -> write_operand st operand destination
  | Operation { operation; type_arguments; operands } ->
      let type_arguments, value_arguments = split_arguments st type_arguments in
      ignore
        (Intrinsics.lower ~checks:st.context.checks ~value_arguments ?reported:(reported_site st)
           st.context.env st.builder st.context.types operation ~type_arguments
           (List.map
              (fun operand ->
                let operand_ty = operand_type st operand in
                if
                  Storage.match_storage_element operand_ty <> None
                  || Storage.match_view_element operand_ty <> None
                then Intrinsics.Place (operand_place st operand)
                else Intrinsics.Value (value st operand))
              operands)
           ~destination:(Some destination) ~site:(site_of st origin))
  | Compare { comparison; left; right } ->
      assign (Binary (binary comparison, value st left, value st right))
  | Not inner -> assign (Unary (Not, value st inner))
  | Construct { variant; fields } ->
      let fields =
        List.map
          (fun (name, (field : Mir.operand option)) ->
            match field with
            | Some field -> (name, value st field)
            | None ->
                let default, default_ty = field_default_place st ty ~variant ~field:name in
                (name, Lowering.owned st default default_ty))
          fields
      in
      assign (Build { ty; variant; fields })
  | Array elements ->
      List.iteri
        (fun index element ->
          Emit_c.Builder.emit st.builder
            (Assign
               ( Lowered.project destination (Index (Lowered.make_uint64_constant index)),
                 Use (value st element) )))
        elements
  | Is_variant { place = tested; variant } -> assign (Is_variant (place st tested, variant))
  | Convert { conversion = Widen; value = inner; _ } -> write_operand st inner destination
  | Convert { conversion = To_integer | From_integer; _ } ->
      Definitions.bug "a conversion that exists only in specifications"
  | To_any { value = inner; trait; evidence } ->
      let impl, type_arguments =
        Targets.resolve_impl st.context st.frame.code.substitution ~trait
          ~self_type:(Mir.operand_type inner) ~evidence
      in
      Targets.any_into st ~any_ty:ty ~inner_ty:(operand_type st inner) ~impl ~type_arguments
        ~value:(operand_place st inner) destination
  | Copy source ->
      Drop_and_copy.copy_into st.context.drop_and_copy st.builder ~destination
        ~source:(operand_place st source) ty
  | Function_value { path; type_arguments; _ } -> (
      match ty with
      | Function function_type ->
          let adapter : Instance.generated =
            Adapter
              {
                function_ = path;
                type_arguments = List.map (ground_argument st) type_arguments;
                ty = function_type;
              }
          in
          assign (Function_value { code = Instance (Generated adapter); environment = None })
      | _ -> Definitions.bug "a function value of type %s" (Ground.to_string ty))
  | Value_parameter parameter -> (
      match ground_argument st (Value (Value_parameter parameter)) with
      | Value number -> assign (Use (Targets.constant_of st ty (Integer_value number)))
      | _ -> Definitions.bug "the value parameter %s is not a number" parameter.name)
  | Lambda { body = index; captures; _ } ->
      let function_type =
        match ty with
        | Function function_type -> function_type
        | _ -> Definitions.bug "a lambda of %s" (Ground.to_string ty)
      in
      let lambdas = (mir st).lambdas in
      let lambda = lambdas.(index) in
      Targets.nested_function st ~function_type
        ~output:
          (match types_ty with
          | Some (Types.Function function_type) -> Some (Types.Returns function_type.output)
          | _ -> None)
        ~captures:
          (List.map
             (fun (capture : Mir.capture) ->
               (place st capture.place, Lowering.ground st capture.type_))
             captures)
        ~body:(fun inner ~captures:capture_places parameter_places ->
          inner.frame <-
            {
              inner.frame with
              mir =
                Some
                  (frame_of_body inner ~owner:(Lowering.innermost_scope inner)
                     ~passed:(List.map (fun (_, mode, _) -> mode) parameter_places)
                     ~lambdas lambda);
            };
          List.iter2 (bind_local inner) lambda.captures capture_places;
          make_owned_locals inner;
          List.iter2
            (fun local (place, _, _) -> bind_local inner local place)
            lambda.parameters parameter_places;
          lower_body inner (Option.get inner.frame.mir))
        destination
  | Specification _ -> Definitions.bug "a specification's expression in code that runs"

and field_default_place st ty ~variant ~field =
  let { Mir.source; form = default } = field_default st ty ~variant ~field in
  Targets.in_type_definition st ~source ty (fun () ->
      let default_ty = Lowering.ground st default.type_ in
      let place = Lowering.temporary st default_ty in
      mir_into st default.value place;
      (place, default_ty))

and mir_into ?(arguments = []) st (expression_mir : Mir.Graph.t) (destination : Lowered.place) =
  let expression_mir = Loop_parts.ended expression_mir in
  let caller = st.frame in
  let exit = Emit_c.Builder.block st.builder in
  let frame =
    frame_of_body st ~returns_into:destination ~lambdas:expression_mir.lambdas expression_mir.body
  in
  st.frame <- { caller with exit = Some (exit, List.length st.scopes); mir = Some frame };
  List.iter2 (bind_local st) expression_mir.body.parameters arguments;
  lower_body st frame;
  Emit_c.Builder.finish st.builder Unreachable;
  Emit_c.Builder.start st.builder exit;
  st.frame <- caller

and call_into st (call : Mir.call) destination ~origin =
  match (resolve_callee st call.callee, call.callee) with
  | Some (path, type_arguments), _ -> (
      let signature = Definitions.signature_of st.context path in
      let substitution = Definitions.bind signature.generics type_arguments in
      let arguments, mask = evaluate_arguments st signature substitution call.arguments in
      match signature.output with
      | Returns _ ->
          Targets.call_instance st
            (Code { path; type_arguments })
            ~signature ~substitution ~arguments ~mask ~destination ()
      | Lends _ -> Definitions.bug "a lending call that lends no part")
  | None, Intrinsic { operation = Holds_invariant; _ } -> (
      match call.arguments with
      | [ value; clause ] -> holds_invariant st ~value ~clause ~destination
      | _ -> Definitions.bug "holds_invariant takes a value and a clause")
  | None, Intrinsic { operation; type_arguments } -> (
      match
        intrinsic st operation ~type_arguments call.arguments ~destination:(Some destination)
          ~site:(site_of st origin)
      with
      | Some _ -> Definitions.bug "a lending intrinsic that lends no part"
      | None -> ())
  | None, Capability_method { capability; name } ->
      let slot, signature = Targets.capability_method st.context capability name in
      let arguments, _ =
        evaluate_arguments st { signature with receiver = None } [] call.arguments
      in
      capability_defaults st ~capability ~name call.arguments arguments;
      if Path.equal capability Definitions.panic_path then
        match arguments with
        | [ (_, _, message) ] ->
            ignore
              (Intrinsics.lower ~checks:st.context.checks st.context.env st.builder st.context.types
                 Crash ~type_arguments:[] [ Intrinsics.Place message ] ~destination:None
                 ~site:(site_of st origin))
        | _ -> Definitions.bug "Panic.crash takes one message"
      else begin
        let c_signature, result = Targets.entry_signature st.context signature in
        let target =
          Lowered.Evidence_call
            {
              evidence = Targets.evidence_of st capability;
              capability;
              slot;
              signature = c_signature;
            }
        in
        Emit_c.Builder.emit st.builder
          (Call
             {
               target;
               arguments =
                 List.filter_map (fun (mode, ty, place) -> Targets.pass st mode ty place) arguments;
               result = Convention.destination result destination;
             });
        if not c_signature.returns then Lowering.unreachable_block st
      end
  | None, Trait_method { trait; name; self_type; _ } -> (
      let any_type =
        match Types.substitute st.frame.code.substitution self_type with
        | Types.Any reference -> reference
        | receiver -> Definitions.bug "a call through any on %s" (Types.show receiver)
      in
      match List.map (argument_place st) call.arguments with
      | (_, _, any) :: arguments ->
          Targets.call_through_any st ~any_type ~trait:trait.trait ~name ~any ~arguments destination
      | [] -> Definitions.bug "a call through any with no receiver")
  | None, Indirect function_value ->
      let function_type =
        match operand_type st function_value with
        | Function function_type -> function_type
        | callee_ty -> Definitions.bug "a call of %s" (Ground.to_string callee_ty)
      in
      let value = operand_place st function_value in
      Targets.call_indirect st ~function_type ~value
        (List.map
           (fun argument ->
             let _, _, place = argument_place st argument in
             place)
           call.arguments)
        destination
  | None, Function _ -> Definitions.bug "a function that does not resolve"

and capability_defaults st ~capability ~name (arguments : Mir.argument list) evaluated =
  if List.mem Mir.Default arguments then begin
    let receiver =
      match Interface.Definition.read_trait_interface st.context.lookups.interface capability with
      | Some interface -> (
          match
            List.find_opt
              (fun (trait_method : Types.trait_method) -> trait_method.method_name = name)
              interface.methods
          with
          | Some declared -> declared.method_receiver
          | None -> Definitions.bug "%s has no method %s" (Path.show capability) name)
      | None -> Definitions.bug "no interface for %s" (Path.show capability)
    in
    let defaults = parameter_defaults st.context (Method { owner = capability; name; receiver }) in
    let caller = st.frame in
    st.frame <-
      {
        caller with
        code =
          {
            caller.code with
            definition = defaults.source.path;
            written = Some (Definitions.read_written st.context defaults.source);
            enclosing_impl = None;
            substitution = [];
          };
        self_place = None;
      };
    List.iteri
      (fun position ((argument : Mir.argument), (_, ty, place)) ->
        match (argument, List.assoc_opt position defaults.form) with
        | Default, Some default ->
            mir_into st default place;
            if not (Lowering.is_trivial st ty) then
              (Lowering.innermost_scope st).owned <-
                Drop_value place :: (Lowering.innermost_scope st).owned
        | Default, None ->
            Definitions.bug "the argument at position %d of `%s.%s` is omitted and has no default"
              position (Path.show capability) name
        | Passed _, _ -> ())
      (List.combine arguments evaluated);
    st.frame <- caller
  end

and holds_invariant st ~value ~clause ~destination =
  let _, value_ty, value_place = argument_place st value in
  let index =
    match clause with
    | Passed { value = Constant { value = Integer index; _ }; _ } -> Z.to_int index
    | _ -> Definitions.bug "holds_invariant with a clause that is not a literal"
  in
  let path =
    match value_ty with
    | Named { path; _ } -> path
    | ty -> Definitions.bug "holds_invariant of %s, which has no invariant" (Ground.to_string ty)
  in
  let ({ source; form = clauses } : Mir.type_clauses Mir.sourced) =
    match Mir.type_clauses_of_path st.context.lookups.mir path with
    | Some clauses -> clauses
    | None -> Definitions.bug "%s has no clauses" (Path.show path)
  in
  let invariant =
    match List.nth_opt clauses.invariants index with
    | Some { clause; is_executable = true; _ } -> Mir.code_of_formula clause
    | Some { is_executable = false; _ } | None ->
        Definitions.bug "%s has no clause %d that runs" (Path.show path) index
  in
  Targets.in_type_definition st ~source value_ty (fun () ->
      mir_into ~arguments:[ value_place ] st invariant destination)

and lend ?(forwards = 0) st part (call : Mir.call) ~origin =
  match (call.callee, if forwards < 8 then forwarded_call st call else None) with
  | Intrinsic { operation; type_arguments }, _ ->
      Hashtbl.replace (mir st).placed_parts part ();
      Lowering.in_statement st (fun () ->
          match
            intrinsic st operation ~type_arguments call.arguments ~destination:None
              ?reported:(reported_site st) ~site:(site_of st origin)
          with
          | Some place -> bind_local st part place
          | None -> Definitions.bug "a lent place from an intrinsic that does not lend")
  | _, Some { setup; call = inner } ->
      List.iter
        (fun (local, type_, (computing : Mir.call)) ->
          let destination = Lowering.held st (Value (Lowering.ground st type_)) in
          Hashtbl.replace (mir st).places local destination;
          call_into st computing destination ~origin)
        setup;
      lend ~forwards:(forwards + 1) st part inner ~origin
  | callee, None ->
      let frame = mir st in
      let lent = lent_call st part in
      let lending part_ty : Lowered.operand list =
        (if Lowering.is_zero_size st part_ty then []
         else
           [
             (match frame.lending with
             | Some { slot = Some slot; part = own; _ }
               when is_forwarded_whole frame part && own = part_ty ->
                 Lowered.Copy slot
             | Some _ when List.mem part frame.ended_after_lend -> Constant Null
             | _ ->
                 Address { place = Lowering.held st ~name:"lent" (Value part_ty); writable = true });
           ])
        @ [
            lent.record;
            Option.value (reported_site st) ~default:(Constant (Site (site_of st origin)));
          ]
      in
      let lent_place (output : Types.result) substitution called =
        let mode, part_ty =
          match output with
          | Lends (mode, ty) -> (mode, Monomorphic.ground st.context.monomorphic substitution ty)
          | Returns _ -> Definitions.bug "a lending call of a method that does not lend"
        in
        emit_mark st Lend_begin lent;
        if Lowering.is_zero_size st part_ty then begin
          called ~lending:(lending part_ty) (discarded st);
          Lowering.held st (Value part_ty)
        end
        else begin
          let pointer =
            Lowering.held st ~name:"part"
              (Pointer { target = Value part_ty; writable = mode = Mut })
          in
          called ~lending:(lending part_ty) pointer;
          Lowered.project pointer Deref
        end
      in
      let place =
        match (resolve_callee st callee, callee) with
        | Some (path, type_arguments), _ ->
            let signature = Definitions.signature_of st.context path in
            let substitution = Definitions.bind signature.generics type_arguments in
            let arguments, mask = evaluate_arguments st signature substitution call.arguments in
            lent_place signature.output substitution (fun ~lending destination ->
                Targets.call_instance st
                  (Code { path; type_arguments })
                  ~signature ~substitution ~arguments ~mask ~lending ~destination ())
        | None, Trait_method { trait; name; self_type; _ } -> (
            let any_type =
              match Types.substitute st.frame.code.substitution self_type with
              | Types.Any reference -> reference
              | receiver -> Definitions.bug "a call through any on %s" (Types.show receiver)
            in
            let _, signature = Targets.dynamic_method st.context trait.trait name in
            match List.map (argument_place st) call.arguments with
            | (_, _, any) :: arguments ->
                lent_place signature.output
                  (Targets.any_substitution st.context ~any:any_type trait.trait)
                  (fun ~lending destination ->
                    Targets.call_through_any st ~any_type ~trait:trait.trait ~name ~any ~arguments
                      ~lending destination)
            | [] -> Definitions.bug "a call through any with no receiver")
        | None, Capability_method _ ->
            Lowering.unsupported ~at:(site_of st origin) "a lending call of a capability's method"
        | None, Indirect _ ->
            Definitions.bug "a lending call of a function value, whose type cannot lend"
        | None, (Function _ | Intrinsic _) -> Definitions.bug "a lending call that does not resolve"
      in
      emit_mark st Lend_called lent;
      bind_local st part place

and lend_part st ~(mode : Types.mode) (part : Mir.yielded) =
  let frame = mir st in
  let lending =
    match frame.lending with
    | Some lending -> lending
    | None -> Definitions.bug "a part lent outside a lending method"
  in
  let owns = Moves.owns frame.moves in
  let outlives =
    outlives_call ~owns
      ~is_view:(fun ty ->
        (Interface.Impls.is_view st.context.lookups.interface ~bounds:Interface.Impls.no_bounds)
          (Types.substitute st.frame.code.substitution ty))
      frame.body
  in
  let lent_in_place (written : Mir.place) : Lowered.place option =
    let lowered = place st written in
    let is_reached_through_pointer =
      match lowered.root with
      | Static _ -> true
      | Local _ -> List.exists (function Lowered.Deref -> true | _ -> false) lowered.projections
    in
    if outlives written && is_reached_through_pointer then Some lowered else None
  in
  let rec write (yielded : Mir.yielded) (destination : Lowered.place) :
      (Lowered.projection list * deferred) list =
    match yielded with
    | Part operand -> (
        let ty = operand_type st operand in
        let made () = if Lowering.is_trivial st ty then [] else [ ([], Deferred_drop ty) ] in
        match operand with
        | Borrow { place = { root = Local local; projections = [] } as written; _ } when owns local
          ->
            Lowering.take st (place st written) ty ~destination;
            made ()
        | Borrow { place = written; _ } -> (
            Emit_c.Builder.emit st.builder (Assign (destination, Use (Copy (place st written))));
            match (lent_in_place written, mode) with
            | Some source, Mut -> [ ([], Deferred_write_back { source; ty }) ]
            | Some _, (Read | Own) -> []
            | None, Mut when outlives written ->
                Definitions.bug "a place lent `mut` that is not reached through a pointer"
            | None, _ ->
                if not (outlives written || Lowering.is_trivial st ty) then
                  Definitions.bug "a lent part of %s that the method owns" (Ground.to_string ty);
                [])
        | Use _ | Take _ | Constant _ ->
            write_operand st operand destination;
            made ())
    | Built { variant; fields; type_; _ } ->
        let ty = Lowering.ground st type_ in
        let field_types = List.assoc variant (variants_of st ty) in
        let built =
          List.map
            (fun (name, (field : Mir.yielded option)) ->
              let field_ty = List.assoc name field_types in
              let value = Lowering.held st (Value field_ty) in
              let deferred =
                match field with
                | Some field -> write field value
                | None ->
                    let default, default_ty = field_default_place st ty ~variant ~field:name in
                    Lowering.take st default default_ty ~destination:value;
                    if Lowering.is_trivial st default_ty then []
                    else [ ([], Deferred_drop default_ty) ]
              in
              ( (name, if Lowering.is_trivial st field_ty then Lowered.Copy value else Move value),
                List.map
                  (fun (inside, deferred) -> (field_of variant name :: inside, deferred))
                  deferred ))
            fields
        in
        Emit_c.Builder.emit st.builder
          (Assign (destination, Build { ty; variant; fields = List.map fst built }));
        let is_indirect variant =
          List.exists
            (fun (shape : Memory_layout.variant_shape) -> shape.name = variant && shape.indirect)
            (match Memory_layout.shape st.context.env ty with Sum shapes -> shapes | _ -> [])
        in
        (match variant with
          | Some variant when is_indirect variant -> [ ([], Deferred_free variant) ]
          | _ -> [])
        @ List.concat_map snd built
  in
  let defer_call intrinsic arguments =
    Emit_c.Builder.emit st.builder
      (Call
         {
           target = Intrinsic intrinsic;
           arguments = lending.record :: arguments;
           result = Discarded;
         })
  in
  let address place : Lowered.operand = Address { place; writable = true } in
  let defer (slot : Lowered.place) (inside, deferred) =
    let target = List.fold_left Lowered.project slot inside in
    match deferred with
    | Deferred_drop ty ->
        defer_call Lend_defer_drop [ Constant (Symbol_address (Any_drop ty)); address target ]
    | Deferred_write_back { source; ty } ->
        defer_call Lend_defer_write_back [ address source; address target; Constant (Size_of ty) ]
    | Deferred_free variant ->
        Emit_c.Builder.emit st.builder
          (Defer_free_block { lend = lending.record; place = target; variant })
  in
  match lending.slot with
  | None -> ()
  | Some slot_pointer -> (
      let pointer : Lowered.operand =
        match part with
        | Part (Borrow { place = written; _ }) when lent_in_place written <> None ->
            Address { place = Option.get (lent_in_place written); writable = mode = Mut }
        | _ ->
            let has_no_slot = Lowering.held st (Raw Bool) in
            Emit_c.Builder.emit st.builder
              (Assign (has_no_slot, Binary (Equal, Copy slot_pointer, Constant Null)));
            Emit_c.Builder.when_ st.builder (Copy has_no_slot) (fun () ->
                Emit_c.Builder.emit st.builder
                  (Call
                     {
                       target = Intrinsic Lend_allocate;
                       arguments =
                         [
                           lending.record;
                           Constant (Size_of lending.part);
                           Constant (Alignment_of lending.part);
                         ];
                       result = Returned slot_pointer;
                     }));
            let slot = Lowered.project slot_pointer Deref in
            List.iter (defer slot) (write part slot);
            Address { place = slot; writable = mode = Mut }
      in
      match Lowering.result_place st with
      | Some result -> Emit_c.Builder.emit st.builder (Assign (result, Use pointer))
      | None -> Definitions.bug "a lending method with no result")

and terminator st region (ending : Mir.Graph.terminator) ~origin =
  match ending with
  | Goto target -> goto st region target
  | Branch { condition; yes; no; _ } ->
      let condition = Lowering.in_statement st (fun () -> value st condition) in
      let yes = jump st region yes and no = jump st region no in
      Emit_c.Builder.branch st.builder condition ~yes ~no;
      Emit_c.Builder.start st.builder (Emit_c.Builder.block st.builder)
  | Unreachable | Written_unreachable -> Lowering.unreachable_block st
  | Todo ->
      let message = "todo reached" in
      Emit_c.Builder.finish st.builder
        (Fail
           {
             failure = Todo;
             message = Constant (Bytes message);
             length = Lowered.make_uint64_constant (String.length message);
             site = site_of st origin;
             reported = None;
           });
      Emit_c.Builder.start st.builder (Emit_c.Builder.block st.builder)
  | Return returned ->
      (match (result_slot st, returned) with
      | Some _, Some (Use { place = { root = Local local; projections = [] }; _ })
        when List.mem local (mir st).returned ->
          ()
      | Some slot, Some returned ->
          Lowering.in_statement st (fun () -> write_operand st returned slot)
      | _ -> ());
      return_from_frame st
  | Iteration_end _ -> continue_loop st
  | Cancel { task; task_end; winner; number; returned } ->
      Option.iter
        (fun target ->
          let rec branch_region (around : region) =
            match (around.ending, task, around.enclosing) with
            | Some (fork, _), Branch { block; _ }, _ when fork = block -> around
            | _, _, Some enclosing -> branch_region enclosing
            | _, _, None -> Definitions.bug "an early exit from a branch outside its block"
          in
          let branch = branch_region region in
          ignore (jump ~entry:branch.start st branch target))
        task_end;
      let value =
        Option.map
          (fun (returned, slot) ->
            let ty = Lowering.ground st (info st slot).type_ in
            let value =
              Lowered.make_local_place (Emit_c.Builder.local st.builder ~name:"returned" (Value ty))
            in
            write_operand st returned value;
            (value, ty, slot))
          returned
      in
      cancel st ~task ~winner ~number ~value
  | Resume { winner; exits; next } ->
      let cases =
        List.mapi
          (fun index (exit : Mir.Graph.early_exit) ->
            (Z.of_int (index + 1), jump st region exit.resume))
          exits
      in
      Emit_c.Builder.finish st.builder
        (Switch { value = Copy (local_place st winner); cases; default = jump st region next });
      Emit_c.Builder.start st.builder (Emit_c.Builder.block st.builder)
  | Yield { mode; part; resume } ->
      Lowering.in_statement st (fun () -> lend_part st ~mode part);
      goto st region resume
  | For { iteration; part; body; after; loop; _ } ->
      claim st region after;
      for_loop st region ~iteration ~part ~body ~loop;
      goto st region after
  | Fork { fork; concurrent = true; branches; join } ->
      concurrent_block st region ~fork ~branches ~join
  | Fork { fork; concurrent = false; branches; join } -> (
      match branches with
      | [] -> Lowering.unreachable_block st
      | first :: _ when not (Lowering.may_fork st) -> goto st region first.entry
      | _ -> (
          let forked =
            List.map
              (fun (branch : Mir.Graph.branch) ->
                Lowering.outlined st ~parts:[] (fun () ->
                    let end_block = Emit_c.Builder.block st.builder in
                    run_region st
                      (new_region st ~enclosing:region ~ending:(fork, end_block))
                      ~entry:(branch.entry, 0);
                    Emit_c.Builder.finish st.builder (Goto end_block);
                    Emit_c.Builder.start st.builder end_block;
                    Emit_c.Builder.finish st.builder (Return None)))
              branches
          in
          Emit_c.Builder.emit st.builder (Fork { branches = forked });
          match join with Some join -> goto st region join | None -> Lowering.unreachable_block st))
  | Join { fork; next } -> (
      match region.ending with
      | Some (ending, end_block) when ending = fork ->
          Emit_c.Builder.finish st.builder (Goto end_block);
          Emit_c.Builder.start st.builder (Emit_c.Builder.block st.builder)
      | _ -> goto st region next)

and loop_body (st : Lowering.state) region ~part ~body (value : Lowered.place) =
  let caller = st.frame in
  st.frame <- region.region_frame;
  bind_local st part value;
  let inner = new_region ~enclosing:region st in
  st.frame <- caller;
  run_region st inner ~entry:(body, 0)

and for_loop st region ~(iteration : Mir.iteration) ~part ~body ~(loop : Mir.loop) =
  let origin = loop.origin in
  let each = loop_body st region ~part ~body in
  match loop.schedule with
  | Concurrent_loop ->
      with_group st (fun group ->
          let spawning =
            {
              Lowering.origin;
              group;
              item = Emit_c.Builder.local st.builder ~name:"item" (Value (Ground.builtin UInt64));
              element = Lowering.ground st (info st part).type_;
            }
          in
          for_each st ~schedule:(Spawned spawning) ~iteration ~each)
  | Parallel_loop -> for_each st ~schedule:Chunked ~iteration ~each
  | Core.Sequential -> for_each st ~schedule:Sequential ~iteration ~each

and for_each st ~(schedule : Lowering.schedule) ~(iteration : Mir.iteration)
    ~(each : Lowered.place -> unit) =
  let schedule =
    match schedule with
    | Chunked when not (Lowering.may_fork st) -> Lowering.Sequential
    | own -> own
  in
  let owned_each =
    match schedule with
    | Spawned loop -> fun value -> spawn_with_item st loop value ~owned:true ~each
    | Sequential | Chunked -> each
  in
  match iteration with
  | Range { start = low; stop = high; inclusive } ->
      range_loop st ~schedule ~low ~high ~inclusive ~each
  | Pull { cursor; next } ->
      let cursor = place st cursor in
      Targets.pull_loop st ~option:(result_type st next)
        ~call_next:(fun destination -> call_with_places st next [ cursor ] ~destination)
        ~body:owned_each

and range_loop st ~schedule ~(low : Mir.operand) ~(high : Mir.operand) ~inclusive ~each =
  let element = operand_type st low in
  let scalar = Lowering.scalar_of st element in
  let constant value : Lowered.operand =
    match scalar with
    | Integer integer -> Lowering.constant_int integer (Z.of_int value)
    | Character -> Constant (Character value)
    | _ -> Definitions.bug "a range of %s" (Ground.to_string element)
  in
  let characters = scalar = Character in
  let both first second =
    let answer = Emit_c.Builder.local st.builder (Raw Bool) in
    Emit_c.Builder.emit st.builder
      (Assign (Lowered.make_local_place answer, Binary (Bit_and, first, second)));
    Lowered.Copy (Lowered.make_local_place answer)
  in
  let compare op left right =
    let answer = Emit_c.Builder.local st.builder (Raw Bool) in
    Emit_c.Builder.emit st.builder
      (Assign (Lowered.make_local_place answer, Binary (op, left, right)));
    Lowered.Copy (Lowered.make_local_place answer)
  in
  match schedule with
  | Chunked ->
      let wide = Lowered.Raw (Integer UInt64) in
      let one = Lowering.constant_int UInt64 Z.one in
      let first_value = Lowering.binding st ~name:"start" element in
      let last_value = Lowering.binding st element in
      Emit_c.Builder.emit st.builder (Assign (first_value, Use (value st low)));
      Emit_c.Builder.emit st.builder (Assign (last_value, Use (value st high)));
      let going = Emit_c.Builder.local st.builder (Raw Bool) in
      Emit_c.Builder.emit st.builder
        (Assign
           ( Lowered.make_local_place going,
             Binary ((if inclusive then Less_equal else Less), Copy first_value, Copy last_value) ));
      let inside = Emit_c.Builder.block st.builder and after = Emit_c.Builder.block st.builder in
      let depth = List.length st.scopes in
      Emit_c.Builder.branch st.builder (Copy (Lowered.make_local_place going)) ~yes:inside ~no:after;
      Emit_c.Builder.start st.builder inside;
      let first = Emit_c.Builder.local st.builder ~name:"first" wide
      and last = Emit_c.Builder.local st.builder ~name:"last" wide in
      let low_wide = Emit_c.Builder.local st.builder wide
      and high_wide = Emit_c.Builder.local st.builder wide in
      Emit_c.Builder.emit st.builder
        (Assign (Lowered.make_local_place first, Use (Lowering.constant_int UInt64 Z.zero)));
      Emit_c.Builder.emit st.builder
        (Assign (Lowered.make_local_place low_wide, Convert (Copy first_value, Integer UInt64)));
      Emit_c.Builder.emit st.builder
        (Assign (Lowered.make_local_place high_wide, Convert (Copy last_value, Integer UInt64)));
      Emit_c.Builder.emit st.builder
        (Assign
           ( Lowered.make_local_place last,
             Binary
               ( Subtract,
                 Copy (Lowered.make_local_place high_wide),
                 Copy (Lowered.make_local_place low_wide) ) ));
      if not inclusive then
        Emit_c.Builder.emit st.builder
          (Assign
             ( Lowered.make_local_place last,
               Binary (Subtract, Copy (Lowered.make_local_place last), one) ));
      if characters then
        Emit_c.Builder.when_ st.builder
          (both
             (compare Less (Copy first_value) (constant 0xD800))
             (compare Greater (Copy last_value) (constant 0xDFFF)))
          (fun () ->
            Emit_c.Builder.emit st.builder
              (Assign
                 ( Lowered.make_local_place last,
                   Binary
                     ( Subtract,
                       Copy (Lowered.make_local_place last),
                       Lowering.constant_int UInt64 (Z.of_int 0x800) ) )));
      let body, environment =
        Lowering.outlined st ~parts:[ first; last ] (fun () ->
            let index = Emit_c.Builder.local st.builder ~name:"index" wide in
            Emit_c.Builder.emit st.builder
              (Assign (Lowered.make_local_place index, Use (Copy (Lowered.make_local_place first))));
            let again = Emit_c.Builder.block st.builder
            and step = Emit_c.Builder.block st.builder
            and done_ = Emit_c.Builder.block st.builder in
            Emit_c.Builder.finish st.builder (Goto again);
            Emit_c.Builder.start st.builder again;
            Lowering.in_scope st (fun () ->
                let offset = Lowering.binding st element in
                let bound = Lowering.binding st element in
                Emit_c.Builder.emit st.builder
                  (Assign (offset, Convert (Copy (Lowered.make_local_place index), scalar)));
                Emit_c.Builder.emit st.builder
                  (Assign (bound, Binary (Add, Copy first_value, Copy offset)));
                if characters then
                  Emit_c.Builder.when_ st.builder
                    (both
                       (compare Less (Copy first_value) (constant 0xD800))
                       (compare Greater_equal (Copy bound) (constant 0xD800)))
                    (fun () ->
                      Emit_c.Builder.emit st.builder
                        (Assign (bound, Binary (Add, Copy bound, constant 0x800))));
                Lowering.looping st ~continue_:step ~break_:done_ ~depth (fun () -> each bound));
            Emit_c.Builder.finish st.builder (Goto step);
            Emit_c.Builder.start st.builder step;
            let ended = Emit_c.Builder.local st.builder (Raw Bool) in
            Emit_c.Builder.emit st.builder
              (Assign
                 ( Lowered.make_local_place ended,
                   Binary
                     ( Equal,
                       Copy (Lowered.make_local_place index),
                       Copy (Lowered.make_local_place last) ) ));
            let next = Emit_c.Builder.block st.builder in
            Emit_c.Builder.branch st.builder
              (Copy (Lowered.make_local_place ended))
              ~yes:done_ ~no:next;
            Emit_c.Builder.start st.builder next;
            Emit_c.Builder.emit st.builder
              (Assign
                 ( Lowered.make_local_place index,
                   Binary (Add, Copy (Lowered.make_local_place index), one) ));
            Emit_c.Builder.finish st.builder (Goto again);
            Emit_c.Builder.start st.builder done_;
            Emit_c.Builder.finish st.builder (Return None))
      in
      Emit_c.Builder.emit st.builder
        (Fork_range
           {
             body;
             environment;
             first = Copy (Lowered.make_local_place first);
             last = Copy (Lowered.make_local_place last);
           });
      Emit_c.Builder.finish st.builder (Goto after);
      Emit_c.Builder.start st.builder after
  | Sequential | Spawned _ ->
      let loop_value ?name () = Lowering.binding st ?name element in
      let index = loop_value ~name:"index" () in
      let stop = loop_value () in
      Emit_c.Builder.emit st.builder (Assign (index, Use (value st low)));
      Emit_c.Builder.emit st.builder (Assign (stop, Use (value st high)));
      let test = Emit_c.Builder.block st.builder
      and inside = Emit_c.Builder.block st.builder
      and step = Emit_c.Builder.block st.builder
      and after = Emit_c.Builder.block st.builder in
      let depth = List.length st.scopes in
      Emit_c.Builder.finish st.builder (Goto test);
      Emit_c.Builder.start st.builder test;
      let going = Emit_c.Builder.local st.builder (Raw Bool) in
      Emit_c.Builder.emit st.builder
        (Assign
           ( Lowered.make_local_place going,
             Binary ((if inclusive then Less_equal else Less), Copy index, Copy stop) ));
      Emit_c.Builder.branch st.builder (Copy (Lowered.make_local_place going)) ~yes:inside ~no:after;
      Emit_c.Builder.start st.builder inside;
      Lowering.looping st ~continue_:step ~break_:after ~depth (fun () ->
          let run value =
            Lowering.in_scope st (fun () ->
                let bound = loop_value () in
                Emit_c.Builder.emit st.builder (Assign (bound, value));
                each bound)
          in
          match schedule with
          | Spawned loop ->
              let item = Lowered.make_local_place loop.item in
              Emit_c.Builder.emit st.builder (Assign (item, Convert (Copy index, Integer UInt64)));
              spawn_iteration st loop ~not_spawned:ignore (fun () ->
                  run (Convert (Copy item, scalar)))
          | Sequential | Chunked -> run (Use (Copy index)));
      Emit_c.Builder.finish st.builder (Goto step);
      Emit_c.Builder.start st.builder step;
      if inclusive then begin
        let last = Emit_c.Builder.local st.builder (Raw Bool) in
        Emit_c.Builder.emit st.builder
          (Assign (Lowered.make_local_place last, Binary (Equal, Copy index, Copy stop)));
        let next = Emit_c.Builder.block st.builder in
        Emit_c.Builder.branch st.builder (Copy (Lowered.make_local_place last)) ~yes:after ~no:next;
        Emit_c.Builder.start st.builder next
      end;
      Emit_c.Builder.emit st.builder (Assign (index, Binary (Add, Copy index, constant 1)));
      if characters then
        Emit_c.Builder.when_ st.builder
          (compare Equal (Copy index) (constant 0xD800))
          (fun () -> Emit_c.Builder.emit st.builder (Assign (index, Use (constant 0xE000))));
      Emit_c.Builder.finish st.builder (Goto test);
      Emit_c.Builder.start st.builder after

let fill_defaults (st : Lowering.state) (mask : Lowered.place) (body : Mir.Graph.body)
    ~(defaults : (int * Mir.Graph.t) list) (places : Lowered.place list) =
  let builder = st.builder in
  let bit = ref (-1) in
  List.mapi
    (fun position (parameter, arrived) ->
      let mode, name, type_ = parameter_of body parameter in
      match List.assoc_opt position defaults with
      | None -> arrived
      | Some default ->
          incr bit;
          let bit = !bit in
          let ty = Lowering.ground st type_ in
          let passed_bit = Emit_c.Builder.local builder (Raw (Integer UInt64))
          and is_omitted = Emit_c.Builder.local builder (Raw Bool) in
          Emit_c.Builder.emit builder
            (Assign
               ( Lowered.make_local_place passed_bit,
                 Binary (Bit_and, Copy mask, Lowering.constant_int UInt64 (Z.shift_left Z.one bit))
               ));
          Emit_c.Builder.emit builder
            (Assign
               ( Lowered.make_local_place is_omitted,
                 Binary
                   ( Equal,
                     Copy (Lowered.make_local_place passed_bit),
                     Lowering.constant_int UInt64 Z.zero ) ));
          let fill = Emit_c.Builder.block builder and after = Emit_c.Builder.block builder in
          let unless_passed other =
            Emit_c.Builder.branch builder
              (Copy (Lowered.make_local_place is_omitted))
              ~yes:fill ~no:other
          in
          let place =
            if mode = Own && not (Lowering.is_trivial st ty) then begin
              let owned_here =
                Lowered.make_local_place (Emit_c.Builder.local builder ?name (Value ty))
              in
              let passed_block = Emit_c.Builder.block builder in
              unless_passed passed_block;
              Emit_c.Builder.start builder passed_block;
              Emit_c.Builder.emit builder (Assign (owned_here, Use (Move arrived)));
              Emit_c.Builder.finish builder (Goto after);
              Emit_c.Builder.start builder fill;
              Lowering.in_statement st (fun () -> mir_into st default owned_here);
              owned_here
            end
            else begin
              let default_value () =
                Lowering.flagged_binding st ty ~flag:(Lowered.make_local_place is_omitted)
              in
              unless_passed after;
              Emit_c.Builder.start builder fill;
              Lowering.in_statement st (fun () ->
                  match arrived with
                  | { projections = [ Deref ]; root = Local pointer } ->
                      let value = default_value () in
                      mir_into st default value;
                      Emit_c.Builder.emit builder
                        (Assign
                           ( Lowered.make_local_place pointer,
                             Use (Address { place = value; writable = true }) ))
                  | place when mode = Own || Lowering.is_trivial st ty -> mir_into st default place
                  | place ->
                      let value = default_value () in
                      mir_into st default value;
                      Emit_c.Builder.emit builder (Assign (place, Use (Copy value))));
              arrived
            end
          in
          Emit_c.Builder.finish builder (Goto after);
          Emit_c.Builder.start builder after;
          place)
    (List.combine body.parameters places)

let lower_code (st : Lowering.state) path ~parameters ?lending () =
  let code_mir = Loop_parts.ended (mir_of st.context path) in
  let frame =
    frame_of_body st ~owner:(Lowering.innermost_scope st) ?lending ~lambdas:code_mir.lambdas
      code_mir.body
  in
  st.frame <- { st.frame with mir = Some frame };
  Option.iter (fun (lending : Lowering.lending) -> st.lend_record <- Some lending.record) lending;
  List.iter2 (bind_local st) code_mir.body.parameters parameters;
  make_owned_locals st;
  lower_body st frame
