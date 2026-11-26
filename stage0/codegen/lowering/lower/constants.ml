let ( let* ) = Option.bind

let collect_all values =
  List.fold_right
    (fun value rest ->
      let* value = value in
      let* rest = rest in
      Some (value :: rest))
    values (Some [])

let make_static_integer (kind : Memory_layout.integer) value =
  let low, high = Memory_layout.compute_integer_range kind in
  if Z.leq low value && Z.leq value high then Some (Lowered.Static_scalar (Integer (kind, value)))
  else None

let find_integer_kind (state : Lowering.state) ty =
  match (Memory_layout.of_type state.context.env ty).form with
  | Scalar (Integer kind) -> Some kind
  | _ -> None

let make_static_bool value = Some (Lowered.Static_scalar (Bool value))

let fold_arithmetic state ty (operation : Intrinsic.scalar) (left : Lowered.static_value)
    (right : Lowered.static_value) =
  match (left, right) with
  | Static_scalar (Integer (kind, x)), Static_scalar (Integer (_, y)) -> (
      let bits = 8 * Memory_layout.compute_integer_size kind in
      let fold_number value =
        let* kind = find_integer_kind state ty in
        make_static_integer kind value
      in
      let fold_shift apply_shift =
        if Z.sign y >= 0 && Z.lt y (Z.of_int bits) then fold_number (apply_shift x (Z.to_int y))
        else None
      in
      match operation with
      | Add -> fold_number (Z.add x y)
      | Subtract -> fold_number (Z.sub x y)
      | Multiply -> fold_number (Z.mul x y)
      | Divide -> if Z.equal y Z.zero then None else fold_number (Z.div x y)
      | Remainder -> if Z.equal y Z.zero then None else fold_number (Z.rem x y)
      | Bit_and -> fold_number (Z.logand x y)
      | Bit_or -> fold_number (Z.logor x y)
      | Bit_xor -> fold_number (Z.logxor x y)
      | Shift_left -> fold_shift Z.shift_left
      | Shift_right -> fold_shift Z.shift_right
      | _ -> None)
  | Static_scalar (Float64 x), Static_scalar (Float64 y) -> (
      let fold_number value = Some (Lowered.Static_scalar (Float64 (Int64.bits_of_float value))) in
      let x = Int64.float_of_bits x and y = Int64.float_of_bits y in
      match operation with
      | Add -> fold_number (x +. y)
      | Subtract -> fold_number (x -. y)
      | Multiply -> fold_number (x *. y)
      | Divide -> fold_number (x /. y)
      | _ -> None)
  | Static_scalar (Float32 x), Static_scalar (Float32 y) -> (
      let fold_number value = Some (Lowered.Static_scalar (Float32 (Int32.bits_of_float value))) in
      let x = Int32.float_of_bits x and y = Int32.float_of_bits y in
      match operation with
      | Add -> fold_number (x +. y)
      | Subtract -> fold_number (x -. y)
      | Multiply -> fold_number (x *. y)
      | Divide -> fold_number (x /. y)
      | _ -> None)
  | _ -> None

let fold_negation (value : Lowered.static_value) =
  match value with
  | Static_scalar (Integer (kind, x)) -> make_static_integer kind (Z.neg x)
  | Static_scalar (Float64 x) ->
      Some
        (Lowered.Static_scalar (Float64 (Int64.bits_of_float (Float.neg (Int64.float_of_bits x)))))
  | Static_scalar (Float32 x) ->
      Some
        (Lowered.Static_scalar (Float32 (Int32.bits_of_float (Float.neg (Int32.float_of_bits x)))))
  | _ -> None

let fold_comparison (comparison : Language.Comparison.t) (left : Lowered.static_value)
    (right : Lowered.static_value) =
  match (left, right) with
  | Static_scalar (Integer (_, x)), Static_scalar (Integer (_, y)) ->
      make_static_bool
        (match comparison with
        | Equal -> Z.equal x y
        | Not_equal -> not (Z.equal x y)
        | Less -> Z.lt x y
        | Less_equal -> Z.leq x y
        | Greater -> Z.gt x y
        | Greater_equal -> Z.geq x y)
  | Static_scalar (Bool x), Static_scalar (Bool y) -> (
      match comparison with
      | Equal -> make_static_bool (x = y)
      | Not_equal -> make_static_bool (x <> y)
      | Less | Less_equal | Greater | Greater_equal -> None)
  | _ -> None

let call_depth = 8
let step_limit = 10_000

let rec project_static_value (value : Lowered.static_value) (projections : Mir.projection list) =
  match (projections, value) with
  | [], _ -> Some value
  | Field name :: rest, Static_record fields ->
      let* field = List.assoc_opt name fields in
      project_static_value field rest
  | Variant_field { variant; field } :: rest, Static_variant (built, fields) when built = variant ->
      let* field = List.assoc_opt field fields in
      project_static_value field rest
  | _ -> None

let fold_literal state ty (constant : Mir.constant) =
  let fold_number literal =
    match Targets.lower_literal state ty literal with
    | Constant scalar -> Some (Lowered.Static_scalar scalar)
    | _ -> None
  in
  match constant with
  | Integer integer -> fold_number (Integer_value integer)
  | Float float -> fold_number (Float_value float)
  | Boolean boolean -> make_static_bool boolean
  | Unit -> None

let enter_evaluated (context : Definitions.context) ~item ~(source : Resolve.Names.key) =
  Lowering.enter_item context ~item
    {
      (Definitions.make_unwritten_code ~definition:source.path ~substitution:Types.no_substitution
         ~result:(Returns Types.unit))
      with
      written = Some (Definitions.read_written context source);
    }

let make_evaluated_state (context : Definitions.context) (evaluated : Lowered.Item.t) =
  let source, mir, ty =
    match evaluated with
    | Constant path -> (
        match Mir.read_initializer_graph context.lookups.mir path with
        | Some { source; form = mir } ->
            ( source,
              mir,
              Monomorphic.ground context.monomorphic Types.no_substitution
                (Interface.Definition.read_constant_type context.lookups.interface path) )
        | None -> Definitions.raise_bug "%s is not a constant" (Path.show path))
    | Assertion { definition; condition } -> (
        match
          match Mir.read_code context.lookups.mir definition with
          | Some _ as code -> code
          | None -> Mir.read_initializer context.lookups.mir definition
        with
        | Some { source; form = code } -> (
            match List.assoc_opt condition (Mir.list_evaluated_asserts code) with
            | Some asserted -> (source, Mir.expand asserted, Ground.make_builtin Bool)
            | None ->
                Definitions.raise_bug "%s has no assertion by evaluation at %d"
                  (Path.show definition) condition)
        | None -> Definitions.raise_bug "%s has no code" (Path.show definition))
    | item -> Definitions.raise_bug "%s is not evaluated" (Lowered.Item.to_string item)
  in
  (enter_evaluated context ~item:(Evaluator evaluated) ~source, mir, ty)

let rec fold_evaluated context ~visiting (evaluated : Lowered.Item.t) =
  let state, mir, ty = make_evaluated_state context evaluated in
  let visiting = match evaluated with Constant path -> path :: visiting | _ -> visiting in
  (ty, fold_body ~visiting ~depth:call_depth ~steps:(ref step_limit) state mir [])

and fold_body ~visiting ~depth ~steps state (mir : Mir.Graph.t)
    (arguments : Lowered.static_value list) =
  let body = mir.body in
  let locals = Hashtbl.create 16 in
  let* () =
    if List.length arguments = List.length body.parameters then begin
      List.iter2 (Hashtbl.replace locals) body.parameters arguments;
      Some ()
    end
    else None
  in
  let ground_local_type local = Lowering.ground state body.locals.(local).type_ in
  let read (place : Mir.place) =
    let* whole =
      match place.root with
      | Local local -> Hashtbl.find_opt locals local
      | Constant path ->
          if List.exists (Path.equal path) visiting then None
          else snd (fold_evaluated state.context ~visiting (Constant path))
      | Literal { value; type_ } ->
          Some
            (Targets.make_static_literal state.context.monomorphic (Lowering.ground state type_)
               value)
    in
    project_static_value whole place.projections
  in
  let fold_operand : Mir.operand -> Lowered.static_value option = function
    | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> read place
    | Immediate { value; type_ } -> fold_literal state (Lowering.ground state type_) value
  in
  let fold_rvalue target : Mir.rvalue -> Lowered.static_value option = function
    | Operand value | Copy value -> fold_operand value
    | Operation { operation = Negate; operands = [ inner ]; _ } ->
        let* inner = fold_operand inner in
        fold_negation inner
    | Operation { operation; operands = [ left; right ]; _ } ->
        let* left = fold_operand left in
        let* right = fold_operand right in
        fold_arithmetic state (ground_local_type target) operation left right
    | Compare { comparison; left; right } ->
        let* left = fold_operand left in
        let* right = fold_operand right in
        fold_comparison comparison left right
    | Not inner -> (
        let* inner = fold_operand inner in
        match inner with Static_scalar (Bool x) -> make_static_bool (not x) | _ -> None)
    | Construct { variant; fields; _ } -> (
        let* fields =
          collect_all
            (List.map
               (fun (name, field) ->
                 let* field = field in
                 let* value = fold_operand field in
                 Some (name, value))
               fields)
        in
        match variant with
        | Some variant -> Some (Lowered.Static_variant (variant, fields))
        | None -> Some (Static_record fields))
    | Array elements ->
        let* elements = collect_all (List.map fold_operand elements) in
        Some (Lowered.Static_array elements)
    | Parameter_default { definition; position; substitution } ->
        let default =
          Mir.read_parameter_default_graph state.context.lookups.mir ~definition ~position
        in
        fold_body ~visiting ~depth ~steps
          (Lowering.enter state.context ~builder:state.builder
             (Lowering.make_frame
                (Definitions.make_default_code state.context state.frame.code ~source:default.source
                   ~substitution)))
          default.form []
    | Operation _ | Is_variant _ | Convert _ | Function_value _ | Lambda _ | Value_parameter _
    | Specification _ ->
        None
  in
  let assign (destination : Mir.place option) value =
    match destination with
    | Some { root = Local local; projections = [] } ->
        Hashtbl.replace locals local value;
        Some ()
    | Some _ -> None
    | None -> Some ()
  in
  let fold_call (destination : Mir.place option) (called : Mir.call) =
    match (called.callee.target, called.arguments) with
    | ( Intrinsic { operation = Buffer Storage_with_capacity; type_arguments = [ Type element ] },
        [ { value = capacity; _ } ] ) -> (
        let* capacity = fold_operand capacity in
        match capacity with
        | Static_scalar (Integer (_, capacity)) when Z.fits_int capacity ->
            assign destination
              (Lowered.Static_storage
                 {
                   element = Lowering.ground state element;
                   elements = [];
                   capacity = Z.to_int capacity;
                 })
        | _ -> None)
    | ( Intrinsic { operation = Buffer Storage_push; _ },
        [
          { value = Borrow { place = { root = Local storage; projections = [] }; _ }; _ };
          { value = element; _ };
        ] ) -> (
        let* element = fold_operand element in
        match Hashtbl.find_opt locals storage with
        | Some (Static_storage contents) when List.length contents.elements < contents.capacity ->
            Hashtbl.replace locals storage
              (Static_storage { contents with elements = contents.elements @ [ element ] });
            Some ()
        | _ -> None)
    | ( Intrinsic { operation = Buffer Storage_from_array; type_arguments = Type element :: _ },
        [ { value = array; _ } ] ) -> (
        let* array = fold_operand array in
        match array with
        | Static_array elements ->
            assign destination
              (Lowered.Static_storage
                 {
                   element = Lowering.ground state element;
                   elements;
                   capacity = List.length elements;
                 })
        | _ -> None)
    | Function { path; instantiation }, arguments when depth > 0 ->
        let* { form = callee_mir; _ } = Mir.read_graph state.context.lookups.mir path in
        let callee =
          Lowering.enter state.context ~builder:state.builder
            (Lowering.make_frame
               (Definitions.make_code state.context path
                  (Monomorphic.ground_instantiation state.context.monomorphic
                     state.frame.code.substitution instantiation)))
        in
        let* values =
          collect_all
            (List.map (fun (argument : Mir.argument) -> fold_operand argument.value) arguments)
        in
        let* value = fold_body ~visiting ~depth:(depth - 1) ~steps callee callee_mir values in
        assign destination value
    | _ -> None
  in
  let fold_statement (statement : Mir.Graph.statement) =
    match statement.kind with
    | Basic (Assign { target = { root = Local local; projections = [] } as target; value; _ }) ->
        let* value = fold_rvalue local value in
        assign (Some target) value
    | Basic (Call { destination; call = called }) -> fold_call destination called
    | Basic (Assert condition) -> (
        match fold_operand condition with Some (Static_scalar (Bool true)) -> Some () | _ -> None)
    | Basic
        (Live _ | Dead _ | Loan_start _ | Loan_end _ | Ghost_assert _ | Proof _ | Evaluated_assert _)
      ->
        Some ()
    | Basic (Assign _ | Lend _ | Echo _) | Provide_start _ | Provide_end -> None
  in
  let rec run block =
    if !steps <= 0 then None
    else begin
      decr steps;
      let basic = body.blocks.(block) in
      let* _ = collect_all (List.map fold_statement basic.statements) in
      match basic.terminator with
      | Goto target -> run target
      | Branch { condition; yes; no; _ } -> (
          match fold_operand condition with
          | Some (Static_scalar (Bool true)) -> run yes
          | Some (Static_scalar (Bool false)) -> run no
          | _ -> None)
      | Return (Some value) -> fold_operand value
      | Return None
      | For _ | Fork _ | Join _ | Iteration_end _ | Yield _ | Cancel _ | Resume _ | Unreachable
      | Written_unreachable | Todo ->
          None
    end
  in
  run 0

type evaluated = Folded of Lowered.data | Run of Ground.ty

let compile context evaluated =
  match fold_evaluated context ~visiting:[] evaluated with
  | ty, Some value -> Folded { data_item = evaluated; ty; value }
  | ty, None -> Run ty

let write_fully = Well_known.make_path Write_fully

let write_output (state : Lowering.state) output =
  let builder = state.builder in
  let int32 = Ground.make_builtin Int32 in
  let bytes_ty = Storage.make_storage_type (Ground.make_builtin UInt8) in
  let descriptor = Lowering.allocate_temporary state int32 in
  Emit_c.Ir_builder.emit builder (Assign (descriptor, Use (Constant (Integer (Int32, Z.one)))));
  let signature = Definitions.read_signature state.context write_fully in
  let result =
    match signature.output with
    | Returns ty -> Monomorphic.ground state.context.monomorphic Types.no_substitution ty
    | Lends _ -> Definitions.raise_bug "write_fully does not return"
  in
  Targets.lower_item_call state
    (Lowered.Item.make_code write_fully Ground.no_instantiation)
    ~signature ~substitution:Types.no_substitution
    ~arguments:[ (Read, int32, descriptor); (Read, bytes_ty, output) ]
    ~destination:(Lowering.allocate_temporary state result)
    ~site:None ()

let build_evaluator (context : Definitions.context) evaluated : Emit_c.fragment =
  let (state : Lowering.state), mir, ty = make_evaluated_state context evaluated in
  Emit_c.Ir_builder.start state.builder (Emit_c.Ir_builder.allocate_block state.builder);
  Lowering.run_in_scope state (fun () ->
      let place = Lowering.allocate_temporary state ty in
      Mir_form.lower_mir_into state mir place;
      let output = Targets.begin_output state in
      Encoding.encode_call context.env state.builder
        ~output:(Address { place = output; writable = true })
        ty place;
      write_output state output);
  Lowering.finish_item state ~rest:[] ()
