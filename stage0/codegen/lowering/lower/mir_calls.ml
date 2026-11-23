let ground_instantiation (state : Lowering.state) instantiation =
  Monomorphic.ground_instantiation state.context.monomorphic state.frame.code.substitution
    instantiation

let resolve_callee state (callee : Mir.callee) : (Path.t * Ground.instantiation) option =
  match callee.target with
  | Function { path; instantiation } -> Some (path, ground_instantiation state instantiation)
  | Trait_method { evidence = Dynamic; _ } -> None
  | Trait_method { trait; name; receiver; self_type; instantiation; evidence } -> (
      match
        Targets.make_trait_method_item state.context state.frame.code.substitution ~trait ~name
          ~receiver ~self_type ~instantiation ~evidence
      with
      | Code { path; instantiation; _ } -> Some (path, instantiation)
      | _ -> Definitions.raise_bug "a trait method whose item is not code")
  | Capability_method _ | Intrinsic _ | Indirect _ -> None

let read_callee_signature (state : Lowering.state) path instantiation =
  let signature = Definitions.read_signature state.context path in
  (signature, Monomorphic.make_signature_substitution signature instantiation)

let resolve_call_signature state (callee : Mir.callee) =
  match resolve_callee state callee with
  | Some (path, instantiation) ->
      let signature, substitution = read_callee_signature state path instantiation in
      (path, Lowered.Item.make_code path instantiation, signature, substitution)
  | None -> Definitions.raise_bug "a callee that is not a function or a method"

let compute_result_type state (callee : Mir.callee) =
  let path, _, signature, substitution = resolve_call_signature state callee in
  match signature.output with
  | Returns ty -> Monomorphic.ground state.context.monomorphic substitution ty
  | Lends _ -> Definitions.raise_bug "%s does not return a value" (Path.show path)

let lower_call_with_places state (callee : Mir.callee) (places : Lowered.place list) ~destination
    ~site =
  let _, item, signature, substitution = resolve_call_signature state callee in
  let arguments =
    List.map2
      (fun (mode, ty) place ->
        (mode, Monomorphic.ground state.context.monomorphic substitution ty, place))
      (Definitions.list_interface_parameters signature)
      places
  in
  Targets.lower_item_call state item ~signature ~substitution ~arguments ~destination ~site ()

let evaluate_arguments (state : Lowering.state) (signature : Types.signature) substitution
    (arguments : Mir.argument list) =
  let parameters = Definitions.list_interface_parameters signature in
  if List.length parameters <> List.length arguments then
    Definitions.raise_bug "a call with %d arguments for %d parameters" (List.length arguments)
      (List.length parameters);
  List.map2
    (fun (mode, ty) (argument : Mir.argument) ->
      ( mode,
        Monomorphic.ground state.context.monomorphic substitution ty,
        Mir_places.lower_operand_place state argument.value ))
    parameters arguments

let lower_argument_place state ({ mode; value; _ } : Mir.argument) =
  (mode, Mir_places.compute_operand_type state value, Mir_places.lower_operand_place state value)

let lower_shared_update state ~shared ~input ~change ~destination ~site =
  let _, _, shared = lower_argument_place state shared in
  let _, _, input = lower_argument_place state input in
  let _, change_ty, change = lower_argument_place state change in
  let function_type =
    match change_ty with
    | Function function_type -> function_type
    | ty ->
        Definitions.raise_bug "shared_update with a %s, which is not a function"
          (Ground.to_string ty)
  in
  let value_ty, result_ty =
    match function_type.parameters with
    | (_, value_ty) :: _ -> (value_ty, function_type.result)
    | [] -> Definitions.raise_bug "shared_update with a function that takes no value"
  in
  let pointer = Lowered.Copy (Builtin_records.Shared.project_value shared) in
  Emit_c.Ir_builder.emit state.builder
    (Call { target = Intrinsic Shared_lock; arguments = [ pointer ]; result = Discarded });
  let typed =
    Emit_c.Ir_builder.allocate_local state.builder
      (Pointer { target = Value value_ty; writable = true })
  in
  Emit_c.Ir_builder.emit state.builder (Assign (Lowered.make_local_place typed, Use pointer));
  let result =
    match destination with
    | Some destination -> destination
    | None -> Lowering.allocate_temporary state result_ty
  in
  Targets.lower_indirect_call state ~function_type ~value:change ~site:(Some site)
    [ Lowered.make_deref_place typed; input ]
    result;
  Emit_c.Ir_builder.emit state.builder
    (Call { target = Intrinsic Shared_unlock; arguments = [ pointer ]; result = Discarded })

let lower_intrinsic state ?reported (operation : Intrinsic.operation) ~type_arguments
    (arguments : Mir.argument list) ~destination ~site =
  match (operation, arguments) with
  | Runtime Shared_update, [ shared; input; change ] ->
      lower_shared_update state ~shared ~input ~change ~destination ~site;
      None
  | _ ->
      let type_arguments, value_arguments = Mir_places.split_arguments state type_arguments in
      let arguments =
        List.map
          (fun (argument : Mir.argument) ->
            match argument.value with
            | Borrow _ as borrowed ->
                Intrinsics.Place (Mir_places.lower_operand_place state borrowed)
            | passed ->
                let ty = Mir_places.compute_operand_type state passed in
                if Storage.find_storage_element ty <> None || Storage.find_view_element ty <> None
                then Intrinsics.Place (Mir_places.lower_operand_place state passed)
                else Intrinsics.Value (Mir_places.lower_operand state passed))
          arguments
      in
      List.iter
        (fun position ->
          match List.nth arguments position with
          | Intrinsics.Place place -> ignore (Lowering.move_place state place)
          | Value _ -> ())
        (Intrinsics.list_consumed_places operation);
      Intrinsics.lower ~value_arguments ?reported state.context.env state.builder
        state.context.types operation ~type_arguments arguments ~destination ~site
        ~trace:(Lowering.find_panic_trace state)

let read_field_default (state : Lowering.state) (ty : Ground.ty) ~variant ~field :
    Mir.Graph.t Mir.field_default Mir.sourced =
  let path =
    match ty with
    | Named { path; _ } -> path
    | _ -> Definitions.raise_bug "defaults of %s" (Ground.to_string ty)
  in
  match Mir.read_default_graphs state.context.lookups.mir path with
  | Some { source; form = Field_defaults defaults } -> (
      match
        List.find_opt
          (fun (default : Mir.Graph.t Mir.field_default) ->
            default.variant = variant && default.field = field)
          defaults
      with
      | Some default -> { source; form = default }
      | None -> Definitions.raise_bug "%s has no default for %s" (Path.show path) field)
  | Some { form = Parameter_defaults _; _ } | None ->
      Definitions.raise_bug "%s is not a type" (Path.show path)
