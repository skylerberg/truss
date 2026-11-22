let require_mir_frame (state : Lowering.state) =
  match state.frame.mir with
  | Some mir -> mir
  | None -> Definitions.raise_bug "MIR lowering outside a MIR frame"

let read_mir_graph (context : Definitions.context) path : Mir.Graph.t =
  match Mir.read_graph context.lookups.mir path with
  | Some { form; _ } -> form
  | None -> Definitions.raise_bug "%s has no MIR" (Path.show path)

let read_parameter_defaults (context : Definitions.context) path :
    (int * Mir.Graph.t) list Mir.sourced =
  match Mir.read_default_graphs context.lookups.mir path with
  | Some { source; form = Parameter_defaults defaults } -> { source; form = defaults }
  | Some { form = Field_defaults _; _ } | None ->
      Definitions.raise_bug "%s is not a function" (Path.show path)

let extract_parameter (body : Mir.Graph.body) local =
  match body.locals.(local) with
  | { kind = Source { local = core; mode; _ }; type_; _ } -> (mode, Mir.find_local_name core, type_)
  | _ -> Definitions.raise_bug "a parameter that is no source local"

let read_spans state = (Lowering.require_written state).spans

let locate_site state (origin : Core.origin) =
  Lowering.make_site state
    (Source.Definition_span.locate (read_spans state) (Core_walk.locate_origin origin))

let find_reported_site (state : Lowering.state) : Lowered.operand option =
  match state.frame.mir with
  | Some { lending = Some { site; _ }; _ }
    when Path.locate_package state.frame.code.definition = Path.standard_package ->
      Some site
  | _ -> None

let lookup_local_info state local = (require_mir_frame state).body.locals.(local)

let find_core_local state local =
  match (lookup_local_info state local).kind with
  | Source { local; _ } -> Some local
  | Temporary | Lent _ -> None

let find_local_name state local = Option.bind (find_core_local state local) Mir.find_local_name

let bind_local state local place =
  Hashtbl.replace (require_mir_frame state).places local place;
  if find_core_local state local = Some Self then state.frame.self_place <- Some place

let find_result_slot state =
  match (require_mir_frame state).returns_into with
  | Some destination -> Some destination
  | None -> Lowering.find_result_place state

let rec locate_local state local : Lowered.place =
  match find_result_slot state with
  | Some slot when List.mem local (require_mir_frame state).returned ->
      bind_local state local slot;
      slot
  | _ -> allocate_place state local

and allocate_place state local : Lowered.place =
  let ty = Lowering.ground state (lookup_local_info state local).type_ in
  let place = Lowering.allocate_local state ?name:(find_local_name state local) (Value ty) in
  bind_local state local place;
  place

let lookup_local_place state local : Lowered.place =
  match Hashtbl.find_opt (require_mir_frame state).places local with
  | Some place -> place
  | None -> locate_local state local

let convert_comparison : Language.Comparison.t -> Lowered.comparison = function
  | Equal -> Equal
  | Not_equal -> Not_equal
  | Less -> Less
  | Less_equal -> Less_equal
  | Greater -> Greater
  | Greater_equal -> Greater_equal

let ground_argument (state : Lowering.state) argument =
  Monomorphic.ground_argument state.context.monomorphic state.frame.code.substitution argument

let split_arguments state type_arguments =
  let ground_arguments = List.map (ground_argument state) type_arguments in
  ( List.filter_map (function Ground.Type ty -> Some ty | _ -> None) ground_arguments,
    List.filter_map (function Ground.Value value -> Some value | _ -> None) ground_arguments )

let fail_out_of_bounds state ~origin condition message =
  Emit_c.Ir_builder.emit state.Lowering.builder
    (Fail_obligation_when
       {
         test = Emit_c.Ir_builder.evaluate_test state.builder condition;
         message = Constant (Bytes message);
         length = Lowered.make_uint64_constant (String.length message);
         site = locate_site state origin;
         reported = find_reported_site state;
         trace = None;
       })

type sequence =
  | Buffer of { buffer : Lowered.place; element : Ground.ty }
  | Inline_array of { array : Lowered.place; element : Ground.ty; count : Z.t; is_empty : bool }

let find_sequence state (place : Lowered.place) (sequence : Types.ty) =
  match Lowering.ground state sequence with
  | Named { path; arguments = [ Type element; Value count ] } as ty
    when Well_known.find_builtin_type path = Some Array ->
      Inline_array
        {
          array = place;
          element;
          count;
          is_empty = Memory_layout.has_zero_size state.context.env ty;
        }
  | Named { path; arguments = Type element :: _ } as ty when Well_known.is_buffer_sequence path -> (
      match (Memory_layout.of_type state.context.env ty).form with
      | Struct [ field ] -> Buffer { buffer = Lowered.project place (Field field.name); element }
      | _ ->
          Definitions.raise_bug "the sequence `%s` holds more than one built-in buffer"
            (Ground.to_string ty))
  | ty ->
      Definitions.raise_bug "an element or a range of `%s`, which is not a sequence"
        (Ground.to_string ty)

let lower_element state place index ~sequence ~origin =
  match find_sequence state place sequence with
  | Buffer { buffer; _ } ->
      fail_out_of_bounds state ~origin
        (Test (Greater_equal, index, Copy (Storage.project_length buffer)))
        "index out of bounds";
      Storage.index_element buffer index
  | Inline_array { array; count; is_empty; _ } ->
      fail_out_of_bounds state ~origin
        (Test (Greater_equal, index, Lowered.make_uint64_constant (Z.to_int count)))
        "index out of bounds";
      if is_empty then array else Lowered.project array (Index index)

let lower_range state place start stop ~sequence ~origin =
  let first_element, length, element =
    match find_sequence state place sequence with
    | Buffer { buffer; element } ->
        ( (if Memory_layout.has_zero_size state.context.env element then
             Lowered.Constant Storage.empty_buffer
           else Address { place = Storage.index_element buffer start; writable = false }),
          Lowered.Copy (Storage.project_length buffer),
          element )
    | Inline_array { array; element; count; is_empty } ->
        ( (if is_empty then Lowered.Constant Storage.empty_buffer
           else Address { place = Lowered.project array (Index start); writable = false }),
          Lowered.make_uint64_constant (Z.to_int count),
          element )
  in
  Option.iter
    (fun stop ->
      fail_out_of_bounds state ~origin (Test (Greater, stop, length)) "slice out of bounds")
    stop;
  let stop = Option.value stop ~default:length in
  fail_out_of_bounds state ~origin (Test (Greater, start, stop)) "slice out of bounds";
  let view_type = Storage.make_view_type element in
  let view = Lowering.allocate_temporary state view_type in
  let count = Lowering.allocate_temporary state (Ground.make_builtin UInt64) in
  Emit_c.Ir_builder.emit state.builder (Assign (count, Binary (Subtract, stop, start)));
  Emit_c.Ir_builder.emit state.builder
    (Assign (view, Storage.build_view view_type ~buffer:first_element ~length:(Copy count)));
  let slice_type : Ground.ty =
    Named { path = Well_known.make_path Slice; arguments = [ Type element ] }
  in
  let slice = Lowering.allocate_temporary state slice_type in
  (match (Memory_layout.of_type state.context.env slice_type).form with
  | Struct [ field ] ->
      Emit_c.Ir_builder.emit state.builder
        (Assign
           (slice, Build { ty = slice_type; variant = None; fields = [ (field.name, Copy view) ] }))
  | _ -> Definitions.raise_bug "a `Slice` that is not one view");
  slice

let rec lower_place state (written : Mir.place) : Lowered.place =
  let root =
    match written.root with
    | Local local -> lookup_local_place state local
    | Constant path -> Targets.lower_static_constant state path
    | Literal { value; type_ } ->
        Targets.lower_literal_place state (Lowering.ground state type_) value
  in
  List.fold_left
    (fun place (projection : Mir.projection) ->
      match projection with
      | Field field -> Lowered.project place (Field field)
      | Variant_field { variant; field } -> Lowered.project place (Variant_field { variant; field })
      | Element { index; sequence; origin; _ } ->
          lower_element state place (lower_index state index) ~sequence ~origin
      | Range { start; stop; sequence; origin; _ } ->
          lower_range state place (lower_index state start)
            (Option.map (lower_index state) stop)
            ~sequence ~origin)
    root written.projections

and lower_index state (index : Mir.operand) : Lowered.operand =
  match index with
  | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> Copy (lower_place state place)
  | Immediate { value = Integer number; _ } -> Lowered.make_uint64_constant (Z.to_int number)
  | Immediate { value = Unit | Float _ | Boolean _; _ } ->
      Definitions.raise_bug "an index that is not an integer"

let list_variants (state : Lowering.state) (ty : Ground.ty) :
    (string option * (string * Ground.ty) list) list =
  let ground_fields fields =
    List.map
      (fun (name, (member : Memory_layout.member)) ->
        match member with
        | Typed field_ty -> (name, field_ty)
        | Raw _ ->
            Definitions.raise_bug "a field %s of %s that no Truss type names" name
              (Ground.to_string ty))
      fields
  in
  match Memory_layout.compute_shape state.context.env ty with
  | Record fields -> [ (None, ground_fields fields) ]
  | Sum variants ->
      List.map
        (fun (variant_shape : Memory_layout.variant_shape) ->
          (Some variant_shape.name, ground_fields variant_shape.fields))
        variants
  | Scalar _ | Array _ ->
      Definitions.raise_bug "the fields of %s, which has none" (Ground.to_string ty)

let make_body_frame (state : Lowering.state) ?owner ?returns_into ?lending
    ?(passed : Language.Mode.t list option) ~lambdas (body : Mir.Graph.body) : Lowering.mir_frame =
  let find_passed_mode local : Language.Mode.t option =
    Option.bind passed (fun modes ->
        Option.map (List.nth modes) (List.find_index (Int.equal local) body.parameters))
  in
  let needs_drop (path : Moves.path) =
    let rec find_path_type ty = function
      | [] -> Some ty
      | projection :: rest -> (
          let member =
            match
              (Memory_layout.compute_shape state.context.env ty, (projection : Mir.projection))
            with
            | Record fields, Field name -> List.assoc_opt name fields
            | Sum variants, Variant_field { variant; field } ->
                Option.bind
                  (List.find_opt
                     (fun (shape : Memory_layout.variant_shape) -> shape.name = variant)
                     variants)
                  (fun (shape : Memory_layout.variant_shape) -> List.assoc_opt field shape.fields)
            | _ -> None
          in
          match member with Some (Typed field_ty) -> find_path_type field_ty rest | _ -> None)
    in
    match
      find_path_type (Lowering.ground state body.locals.(path.local).type_) path.projections
    with
    | Some ty -> not (Lowering.is_trivial state ty)
    | None -> false
  in
  let moves = Moves.analyse ~find_passed:find_passed_mode ~tracks:needs_drop body in
  let after_lend = Array.make (Array.length body.blocks) false in
  let rec reach block =
    if not after_lend.(block) then begin
      after_lend.(block) <- true;
      List.iter reach (Mir.Graph.list_block_successors body block)
    end
  in
  Array.iter
    (fun (basic : Mir.Graph.basic_block) ->
      match basic.terminator with Yield { resume; _ } -> reach resume | _ -> ())
    body.blocks;
  let list_statements_where is_in_block select =
    List.concat
      (List.mapi
         (fun block (basic : Mir.Graph.basic_block) ->
           if is_in_block block then List.concat_map select basic.statements else [])
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
              (Emit_c.Ir_builder.allocate_local state.builder ~is_zeroed:true (Raw Bool)) ))
        (Moves.list_flagged moves);
    move_state = Moves.copy_entry_state moves 0;
    lending;
    called_parts =
      list_statements_where
        (fun _ -> true)
        (fun (statement : Mir.Graph.statement) ->
          match statement.kind with
          | Basic (Lend { call = { callee = { target = Intrinsic _; _ }; _ }; _ }) -> []
          | Basic (Lend { part; _ }) -> [ part ]
          | Basic _ | Provide_start _ | Provide_end -> []);
    lend_records = Hashtbl.create 4;
    placed_parts = Hashtbl.create 4;
    forwarded_locals = 0;
    ended_after_lend = list_statements_where (fun block -> after_lend.(block)) Moves.list_ended;
    after_lend;
    block = 0;
  }

let make_field_projection variant field : Lowered.projection =
  match variant with Some variant -> Variant_field { variant; field } | None -> Field field

let lower_owned_place state (written : Mir.place) =
  match written.root with
  | Literal _ -> Definitions.raise_bug "a literal used as an owned value"
  | Local _ | Constant _ -> lower_place state written

let take_place state (written : Mir.place) =
  let frame = require_mir_frame state in
  frame.taken <- written :: frame.taken;
  lower_owned_place state written

let compute_operand_type state operand = Lowering.ground state (Mir.extract_operand_type operand)

let lower_constant state ty (value : Mir.constant) : Lowered.operand =
  match value with
  | Unit -> Definitions.raise_bug "a unit constant as a value"
  | Integer number -> Targets.lower_literal state ty (Integer_value number)
  | Float number -> Targets.lower_literal state ty (Float_value number)
  | Boolean truth -> Constant (Bool truth)

let lower_operand state (operand : Mir.operand) : Lowered.operand =
  let ty = compute_operand_type state operand in
  match operand with
  | Immediate { value; _ } -> lower_constant state ty value
  | Use { place = written; _ } ->
      Lowering.make_owned_operand state (lower_owned_place state written) ty
  | Take { place = written; _ } -> Lowering.make_owned_operand state (take_place state written) ty
  | Borrow { place = written; _ } -> Copy (lower_place state written)

let lower_operand_place state (operand : Mir.operand) : Lowered.place =
  let ty = compute_operand_type state operand in
  match operand with
  | Borrow { place = written; _ } -> lower_place state written
  | Use { place = { root = Local local; projections = [] } as written; _ }
    when (lookup_local_info state local).kind = Temporary ->
      lower_place state written
  | Use { place = written; _ } ->
      let held = Lowering.allocate_temporary state ty in
      Lowering.take state (lower_owned_place state written) ty ~destination:held;
      held
  | Take { place = written; _ } ->
      let held = Lowering.allocate_temporary state ty in
      Lowering.take state (take_place state written) ty ~destination:held;
      held
  | Immediate { value = Unit; _ } -> Lowering.allocate_temporary state ty
  | Immediate { value; _ } ->
      let held = Lowering.allocate_temporary state ty in
      Emit_c.Ir_builder.emit state.builder (Assign (held, Use (lower_constant state ty value)));
      held

let write_operand state (operand : Mir.operand) (destination : Lowered.place) =
  let ty = compute_operand_type state operand in
  match operand with
  | Immediate { value = Unit; _ } -> ()
  | Immediate { value; _ } ->
      Emit_c.Ir_builder.emit state.builder
        (Assign (destination, Use (lower_constant state ty value)))
  | Use { place = written; _ } ->
      Lowering.take state (lower_owned_place state written) ty ~destination
  | Take { place = written; _ } -> Lowering.take state (take_place state written) ty ~destination
  | Borrow { place = written; _ } ->
      Emit_c.Ir_builder.emit state.builder
        (Assign (destination, Use (Copy (lower_place state written))))

let make_discard_place state = Lowering.allocate_temporary state (Ground.make_builtin Unit)

let compute_mir_place_type state (written : Mir.place) =
  match written with
  | { root = Local local; projections = [] } ->
      Lowering.ground state (lookup_local_info state local).type_
  | _ -> (
      match Lowering.find_place_type state (lower_place state written) with
      | Some (Value ty) -> ty
      | _ -> Definitions.raise_bug "a place of no known type")

let compute_target_type state (target : Mir.place) (value : Mir.rvalue) =
  match (target, value) with
  | _, Operand operand -> compute_operand_type state operand
  | _ -> compute_mir_place_type state target

let reads (value : Mir.rvalue) local =
  let is_in_place (written : Mir.place) = written.root = Local local in
  let is_in_operand (operand : Mir.operand) =
    match operand with
    | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> is_in_place place
    | Immediate _ -> false
  in
  match value with
  | Operand operand | Not operand | Copy operand -> is_in_operand operand
  | Convert { value; _ } | To_any { value; _ } -> is_in_operand value
  | Operation { operands; _ } | Array operands -> List.exists is_in_operand operands
  | Compare { left; right; _ } -> is_in_operand left || is_in_operand right
  | Construct { fields; _ } ->
      List.exists (fun (_, field) -> Option.fold ~none:false ~some:is_in_operand field) fields
  | Is_variant { place; _ } -> is_in_place place
  | Function_value _ | Lambda _ | Value_parameter _ | Specification _ -> false

let alias state local (source : Lowered.place) ~writable =
  let info = lookup_local_info state local in
  if info.has_several_bindings then begin
    let frame = require_mir_frame state in
    let pointer =
      match Hashtbl.find_opt frame.places local with
      | Some { root = Local pointer; projections = [ Deref ] } -> Lowered.make_local_place pointer
      | Some { root = Local pointer; projections = [ Deref; Field field; Deref ] } ->
          { root = Local pointer; projections = [ Deref; Field field ] }
      | _ ->
          let pointer =
            Lowering.allocate_local state ?name:(find_local_name state local)
              (Pointer { target = Value (Lowering.ground state info.type_); writable })
          in
          bind_local state local (Lowered.project pointer Deref);
          pointer
    in
    Emit_c.Ir_builder.emit state.builder
      (Assign (pointer, Use (Address { place = source; writable })))
  end
  else bind_local state local (Lowering.snapshot state source)
