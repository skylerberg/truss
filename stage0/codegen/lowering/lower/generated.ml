let make_generated_state context ~item ~definition ~substitution =
  Lowering.enter_item context ~item
    (Definitions.make_unwritten_code ~definition ~substitution ~result:(Returns Types.unit))

let choose_result_place state result_ty =
  match Lowering.find_result_place state with
  | Some place -> place
  | None -> Lowering.allocate_temporary state result_ty

let allocate_parameters (state : Lowering.state) substitution
    (parameters : Types.parameter_info list) =
  List.map
    (fun (info : Types.parameter_info) ->
      let ty = Monomorphic.ground state.context.monomorphic substitution info.type_ in
      (Lowering.allocate_parameter state ~owned:(info.mode = Own) info.mode ty, info.mode, ty))
    parameters

let load_outer_evidence builder ~evidence index : Lowered.operand =
  let outer = Emit_c.Ir_builder.allocate_local builder Convention.evidence in
  Emit_c.Ir_builder.emit builder
    (Call
       {
         target = Intrinsic Evidence_outer;
         arguments =
           [ Copy (Lowered.make_local_place evidence); Constant (Integer (Int32, Z.of_int index)) ];
         result = Returned (Lowered.make_local_place outer);
       });
  Copy (Lowered.make_local_place outer)

let read_impl_capability context impl =
  let interface = Definitions.read_impl_interface context impl in
  ( interface,
    interface.implements.trait,
    Definitions.list_evidence context Types.no_substitution interface.impl_uses )

let build_entry context (item : Lowered.Item.t) (impl_method : Lowered.Item.impl_method) :
    Emit_c.fragment =
  let { Lowered.Item.impl; name; receiver; type_arguments } = impl_method in
  let path = Lowered.Item.make_method_path impl_method in
  let interface, capability, captured = read_impl_capability context impl in
  let _, capability_signature = Targets.lookup_capability_method context capability name in
  let _, result = Targets.make_entry_signature context capability_signature in
  let method_signature = Definitions.read_signature context path in
  let substitution = Definitions.bind method_signature.generics type_arguments in
  let state = make_generated_state context ~item ~definition:impl ~substitution in
  let builder = state.builder in
  let evidence = Emit_c.Ir_builder.allocate_local builder Convention.evidence in
  Lowering.set_result_slot state result;
  let parameter_places = allocate_parameters state substitution capability_signature.parameters in
  Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder);
  let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
  let implementation =
    Emit_c.Ir_builder.allocate_local builder (Pointer { target = Value self_ty; writable = true })
  in
  if not (Lowering.is_zero_size state self_ty) then
    Emit_c.Ir_builder.emit builder
      (Call
         {
           target = Intrinsic Evidence_implementation;
           arguments = [ Copy (Lowered.make_local_place evidence) ];
           result = Returned (Lowered.make_local_place implementation);
         });
  state.evidence <-
    List.mapi
      (fun position capability -> (capability, load_outer_evidence builder ~evidence position))
      captured;
  let self_mode : Language.Mode.t = match receiver with Instance mode -> mode | Static -> Read in
  let result_ty =
    Monomorphic.ground context.monomorphic Types.no_substitution
      (Types.extract_result_type capability_signature.output)
  in
  Targets.lower_item_call state
    (Lowered.Item.make_code path { Ground.no_instantiation with type_arguments })
    ~signature:method_signature ~substitution
    ~arguments:
      ((self_mode, self_ty, Lowered.make_deref_place implementation)
      :: List.map (fun ((_, place), mode, ty) -> (mode, ty, place)) parameter_places)
    ~destination:(choose_result_place state result_ty)
    ~site:None ();
  Emit_c.Ir_builder.build state.builder
    (Lowering.finish_function state
       ~returns:(capability_signature.output <> Returns Never)
       ~first:[ evidence ]
       ~rest:(List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places)
       ())

let build_locked_entry context (item : Lowered.Item.t) ~capability ~name : Emit_c.fragment =
  let slot, capability_signature = Targets.lookup_capability_method context capability name in
  let c_signature, result = Targets.make_entry_signature context capability_signature in
  let state =
    make_generated_state context ~item ~definition:capability ~substitution:Types.no_substitution
  in
  let builder = state.builder in
  let evidence = Emit_c.Ir_builder.allocate_local builder Convention.evidence in
  Lowering.set_result_slot state result;
  let parameter_places =
    allocate_parameters state Types.no_substitution capability_signature.parameters
  in
  Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder);
  let implementation = load_outer_evidence builder ~evidence 0
  and tasks = load_outer_evidence builder ~evidence 1 in
  let address = Emit_c.Ir_builder.allocate_local builder (Raw (Pointer Opaque)) in
  Emit_c.Ir_builder.emit builder
    (Call
       {
         target = Intrinsic Evidence_implementation;
         arguments = [ Copy (Lowered.make_local_place evidence) ];
         result = Returned (Lowered.make_local_place address);
       });
  let mutex =
    Lowered.make_local_place
      (Emit_c.Ir_builder.allocate_local builder (Value (Ground.make_builtin UInt64)))
  in
  Emit_c.Ir_builder.emit builder
    (Assign (mutex, Convert (Copy (Lowered.make_local_place address), Integer UInt64)));
  let call_tasks method_ =
    let { Well_known.owner; name; _ } = Well_known.locate_method method_ in
    let tasks_capability = Well_known.make_path owner in
    let slot, signature = Targets.lookup_capability_method context tasks_capability name in
    Emit_c.Ir_builder.emit builder
      (Call
         {
           target =
             Evidence_call
               {
                 evidence = tasks;
                 capability = tasks_capability;
                 slot;
                 signature = fst (Targets.make_entry_signature context signature);
               };
           arguments = [ Copy mutex ];
           result = Discarded;
         })
  in
  let result_ty =
    Monomorphic.ground context.monomorphic Types.no_substitution
      (Types.extract_result_type capability_signature.output)
  in
  call_tasks Tasks_lock;
  Emit_c.Ir_builder.emit builder
    (Call
       {
         target =
           Evidence_call { evidence = implementation; capability; slot; signature = c_signature };
         arguments =
           List.filter_map
             (fun ((_, place), mode, ty) -> Targets.pass state mode ty place)
             parameter_places;
         result = Convention.make_destination result (choose_result_place state result_ty);
       });
  call_tasks Tasks_unlock;
  Emit_c.Ir_builder.build state.builder
    (Lowering.finish_function state
       ~returns:(capability_signature.output <> Returns Never)
       ~first:[ evidence ]
       ~rest:(List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places)
       ())

let build_locked_table (context : Definitions.context) (item : Lowered.Item.t) ~capability :
    Lowered.table =
  let interface = Definitions.read_trait_interface context capability in
  {
    table_item = item;
    capability = Some capability;
    entries =
      List.map
        (fun (trait_method : Types.trait_method) ->
          ( Lowered.Item.Generated (Locked_entry { capability; name = trait_method.method_name }),
            fst
              (Targets.make_entry_signature context
                 (Interface.Definition.read_method_signature context.lookups.interface
                    ~owner:capability trait_method)) ))
        interface.methods;
  }

let build_impl_table context (item : Lowered.Item.t) ~impl ~type_arguments : Lowered.table =
  let interface, capability, _ = read_impl_capability context impl in
  let capability_interface = Definitions.read_trait_interface context capability in
  let entries =
    List.map
      (fun (trait_method : Types.trait_method) ->
        let receiver =
          match Types.find_implementing_receiver capability_interface interface trait_method with
          | Some receiver -> receiver
          | None ->
              Definitions.raise_bug "%s does not write %s" (Path.show impl) trait_method.method_name
        in
        ( Lowered.Item.Generated
            (Entry { impl; name = trait_method.method_name; receiver; type_arguments }),
          fst
            (Targets.make_entry_signature context
               (Interface.Definition.read_method_signature context.lookups.interface
                  ~owner:capability trait_method)) ))
      capability_interface.methods
  in
  { table_item = item; capability = Some capability; entries }

let build_real_implementation (state : Lowering.state) ~user capability =
  let impl =
    match
      Interface.Definition.find_real_implementation state.context.lookups.interface capability
    with
    | Some impl -> impl
    | None ->
        Definitions.raise_bug "%s uses %s, which has no real implementation" user
          (Path.show capability)
  in
  let for_type = (Definitions.read_impl_interface state.context impl).for_type in
  let ty = Monomorphic.ground state.context.monomorphic Types.no_substitution for_type in
  let implementation =
    if Lowering.is_zero_size state ty then Lowered.Constant Null
    else begin
      let value = Lowering.allocate_binding state ty in
      let default =
        match
          Interface.Impls.resolve_evidence state.context.lookups.interface Types.no_substitution
            ~self_type:for_type
            ~trait:{ trait = Well_known.make_path Default; trait_arguments = []; associated = [] }
            Bound
        with
        | Impl { impl = default_impl; _ } ->
            Well_known.make_impl_method_path Default_default ~impl:default_impl
        | Bound | Dynamic ->
            Definitions.raise_bug "%s implements %s and has no impl of Default"
              (Types.show for_type) (Path.show capability)
      in
      Targets.lower_item_call state
        (Lowered.Item.make_code default Ground.no_instantiation)
        ~signature:(Definitions.read_signature state.context default)
        ~substitution:Types.no_substitution ~arguments:[] ~destination:value ~site:None ();
      Address { place = value; writable = true }
    end
  in
  Targets.lower_implementation_evidence state ~impl ~type_arguments:[] ~implementation ~site:None

let list_real_implementations (state : Lowering.state) ~user capabilities =
  List.map
    (fun capability ->
      ( capability,
        if Path.equal capability Definitions.panic_path then Lowered.Constant Null
        else build_real_implementation state ~user capability ))
    capabilities

let text_copied_from = Well_known.make_path Text_copied_from

let build_program_main context (item : Lowered.Item.t) main_path : Emit_c.fragment =
  let state =
    make_generated_state context ~item ~definition:main_path ~substitution:Types.no_substitution
  in
  let builder = state.builder in
  let count = Emit_c.Ir_builder.allocate_local builder (Raw (Integer Int32)) in
  let arguments_pointer = Emit_c.Ir_builder.allocate_local builder (Raw (Pointer Opaque)) in
  Lowering.set_result_slot state (Returned (Raw (Integer Int32)));
  Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder);
  let signature = Definitions.read_signature context main_path in
  let list_ty, list_mode =
    match signature.parameters with
    | [ info ] ->
        (Monomorphic.ground context.monomorphic Types.no_substitution info.type_, info.mode)
    | _ -> Definitions.raise_bug "main takes its arguments"
  in
  let storage_field, _, string_ty = Targets.read_list_parts context.monomorphic list_ty in
  let list = Lowering.allocate_temporary state list_ty in
  let lower operation type_arguments arguments destination =
    ignore
      (Intrinsics.lower context.env builder context.types operation ~type_arguments arguments
         ~destination
         ~site:{ definition = main_path; offset = 0 }
         ~trace:None)
  in
  let wanted = Emit_c.Ir_builder.allocate_local builder (Value context.types.uint64) in
  Emit_c.Ir_builder.emit builder
    (Assign
       ( Lowered.make_local_place wanted,
         Convert (Copy (Lowered.make_local_place count), Integer UInt64) ));
  lower (Buffer Storage_with_capacity) [ string_ty ]
    [ Value (Copy (Lowered.make_local_place wanted)) ]
    (Some (Lowered.project list (Field storage_field)));
  Emit_c.Ir_builder.emit_loop builder ~integer:Int32
    ~count:(Copy (Lowered.make_local_place count))
    (fun index ->
      let length = Emit_c.Ir_builder.allocate_local builder (Value context.types.uint64)
      and bytes = Emit_c.Ir_builder.allocate_local builder (Raw (Pointer Opaque)) in
      let call intrinsic arguments result =
        Emit_c.Ir_builder.emit builder
          (Call
             {
               target = Intrinsic intrinsic;
               arguments;
               result = Returned (Lowered.make_local_place result);
             })
      in
      call Program_argument
        [ Copy (Lowered.make_local_place arguments_pointer); Copy (Lowered.make_local_place index) ]
        bytes;
      call Terminated_length [ Copy (Lowered.make_local_place bytes) ] length;
      let view_ty = Storage.make_view_type (Ground.make_builtin UInt8) in
      let view = Lowering.allocate_temporary state view_ty in
      Emit_c.Ir_builder.emit builder
        (Assign
           ( view,
             Storage.build_view view_ty
               ~buffer:(Copy (Lowered.make_local_place bytes))
               ~length:(Copy (Lowered.make_local_place length)) ));
      let text = Lowering.allocate_temporary state string_ty in
      Targets.lower_item_call state
        (Lowered.Item.make_code text_copied_from Ground.no_instantiation)
        ~signature:(Definitions.read_signature context text_copied_from)
        ~substitution:Types.no_substitution
        ~arguments:[ (Read, view_ty, view) ]
        ~destination:text ~site:None ();
      lower (Buffer Storage_push) [ string_ty ]
        [
          Place (Lowered.project list (Field storage_field)); Value (Lowering.move_place state text);
        ]
        None);
  state.evidence <-
    list_real_implementations state ~user:"main"
      (Definitions.list_evidence state.context Types.no_substitution signature.uses);
  let exit_ty =
    match signature.output with
    | Returns ty -> Monomorphic.ground context.monomorphic Types.no_substitution ty
    | _ -> Definitions.raise_bug "main lends"
  in
  let exit = Lowering.allocate_temporary state exit_ty in
  Targets.lower_item_call state
    (Lowered.Item.make_code main_path Ground.no_instantiation)
    ~signature ~substitution:Types.no_substitution
    ~arguments:[ (list_mode, list_ty, list) ]
    ~destination:exit ~site:None ();
  (match
     (Monomorphic.compute_shape context.monomorphic exit_ty, Lowering.find_result_place state)
   with
  | Record [ (field, _) ], Some status ->
      Emit_c.Ir_builder.emit builder
        (Assign (status, Convert (Copy (Lowered.project exit (Field field)), Integer Int32)))
  | _ -> Definitions.raise_bug "an ExitCode that is not a record of one field");
  Emit_c.Ir_builder.build state.builder
    (Lowering.finish_function state ~first:[ count; arguments_pointer ] ~rest:[] ())

let build_test_main context (item : Lowered.Item.t) test_path : Emit_c.fragment =
  let state =
    make_generated_state context ~item ~definition:test_path ~substitution:Types.no_substitution
  in
  Emit_c.Ir_builder.start state.builder (Emit_c.Ir_builder.allocate_block state.builder);
  let signature = Definitions.read_signature context test_path in
  state.evidence <-
    list_real_implementations state ~user:(Path.show test_path)
      (Definitions.list_evidence state.context Types.no_substitution signature.uses);
  Targets.lower_item_call state
    (Lowered.Item.make_code test_path Ground.no_instantiation)
    ~signature ~substitution:Types.no_substitution ~arguments:[]
    ~destination:
      (choose_result_place state
         (Monomorphic.ground context.monomorphic Types.no_substitution Types.unit))
    ~site:None ();
  Lowering.finish_item state ~rest:[] ()

let build_adapter context (item : Lowered.Item.t) ~(function_ : Path.t) ~instantiation
    ~(ty : Ground.function_type) : Emit_c.fragment =
  let signature = Definitions.read_signature context function_ in
  let substitution = Monomorphic.make_signature_substitution signature instantiation in
  let state = make_generated_state context ~item ~definition:function_ ~substitution in
  let builder = state.builder in
  let environment = Emit_c.Ir_builder.allocate_local builder (Raw (Nullable_pointer Opaque)) in
  Lowering.set_result_slot state (Convention.classify_result context.env ty.result);
  let parameter_places =
    List.map
      (fun ((mode : Language.Mode.t), ty) ->
        (Lowering.allocate_parameter state ~owned:(mode = Own) mode ty, mode, ty))
      ty.parameters
  in
  let capabilities = Emit_c.Ir_builder.allocate_local builder Convention.capabilities in
  Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder);
  Lowering.look_up_capabilities state ~table:(Copy (Lowered.make_local_place capabilities)) ty.uses;
  Targets.lower_item_call state
    (Lowered.Item.make_code function_ instantiation)
    ~signature ~substitution
    ~arguments:(List.map (fun ((_, place), mode, ty) -> (mode, ty, place)) parameter_places)
    ~destination:(choose_result_place state ty.result)
    ~site:None ();
  Emit_c.Ir_builder.build state.builder
    (Lowering.finish_function state ~returns:(ty.result <> Never) ~first:[ environment ]
       ~rest:
         (List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places @ [ capabilities ])
       ())

let build_any_entry context (item : Lowered.Item.t) (impl_method : Lowered.Item.impl_method) :
    Emit_c.fragment =
  let { Lowered.Item.impl; name; receiver; type_arguments } = impl_method in
  let path = Lowered.Item.make_method_path impl_method in
  let interface = Definitions.read_impl_interface context impl in
  let trait = interface.implements.trait in
  let trait_signature =
    match
      Interface.Definition.find_trait_method context.lookups.interface trait ~name ~receiver
    with
    | Some trait_method ->
        Interface.Definition.read_method_signature context.lookups.interface ~owner:trait
          trait_method
    | None -> Definitions.raise_bug "%s declares no %s" (Path.show trait) name
  in
  let method_signature = Definitions.read_signature context path in
  let substitution = Definitions.bind method_signature.generics type_arguments in
  let any = Types.substitute_trait substitution interface.implements in
  let _, result, capabilities =
    Targets.make_any_entry_signature context ~any ~trait trait_signature
  in
  let state = make_generated_state context ~item ~definition:impl ~substitution in
  let builder = state.builder in
  let value = Emit_c.Ir_builder.allocate_local builder (Raw (Pointer Opaque)) in
  Lowering.set_result_slot state result;
  let parameter_places = allocate_parameters state substitution method_signature.parameters in
  let evidence = Lowering.list_evidence_parameters state capabilities in
  let lending =
    List.map
      (fun ty -> Emit_c.Ir_builder.allocate_local builder ty)
      (Definitions.list_lending_parameters context substitution method_signature.output)
  in
  Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder);
  let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
  let typed =
    Emit_c.Ir_builder.allocate_local builder (Pointer { target = Value self_ty; writable = true })
  in
  if not (Lowering.is_zero_size state self_ty) then
    Emit_c.Ir_builder.emit builder
      (Assign (Lowered.make_local_place typed, Use (Copy (Lowered.make_local_place value))));
  let self_mode : Language.Mode.t = match receiver with Instance mode -> mode | Static -> Read in
  let destination =
    match (method_signature.output, Lowering.find_result_place state) with
    | _, Some place -> place
    | Returns result_type, None ->
        Lowering.allocate_temporary state
          (Monomorphic.ground context.monomorphic substitution result_type)
    | Lends _, None -> Lowering.allocate_temporary state (Ground.make_builtin Unit)
  in
  Targets.lower_item_call state
    (Lowered.Item.make_code path { Ground.no_instantiation with type_arguments })
    ~signature:method_signature ~substitution
    ~arguments:
      ((self_mode, self_ty, Lowered.make_deref_place typed)
      :: List.map (fun ((_, place), mode, ty) -> (mode, ty, place)) parameter_places)
    ~lending:(List.map (fun local -> Lowered.Copy (Lowered.make_local_place local)) lending)
    ~destination ~site:None ();
  if self_mode = Own then
    Emit_c.Ir_builder.emit builder
      (Call
         {
           target = Intrinsic Free;
           arguments = [ Copy (Lowered.make_local_place value) ];
           result = Discarded;
         });
  Emit_c.Ir_builder.build state.builder
    (Lowering.finish_function state
       ~returns:(method_signature.output <> Returns Never)
       ~first:[ value ]
       ~rest:
         (List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places
         @ evidence @ lending)
       ())

let build_any_table context (item : Lowered.Item.t) ~impl ~type_arguments : Lowered.table =
  let interface = Definitions.read_impl_interface context impl in
  let substitution = Definitions.bind interface.impl_generics type_arguments in
  let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
  let slots = Targets.list_any_slots context ~self:interface.for_type interface.implements in
  let any =
    let implements = Types.substitute_trait substitution interface.implements in
    let for_type = Types.substitute substitution interface.for_type in
    let required =
      List.concat_map
        (fun (bound : Types.trait_reference) ->
          List.filter_map
            (fun (associated : Types.associated_type) ->
              if List.mem_assoc associated.associated_name implements.associated then None
              else
                Some
                  ( associated.associated_name,
                    context.monomorphic.normalize
                      (Types.Projection
                         {
                           base = for_type;
                           trait = Types.substitute_trait substitution bound;
                           name = associated.associated_name;
                         }) ))
            (Definitions.read_trait_interface context bound.trait).associated_types)
        (List.sort_uniq compare (List.map fst slots))
    in
    { implements with associated = implements.associated @ required }
  in
  let entries =
    List.map
      (fun ((bound : Types.trait_reference), (trait_method : Types.trait_method)) ->
        let trait = bound.trait in
        let implementing, implementing_arguments =
          if Path.equal trait interface.implements.trait then (impl, type_arguments)
          else
            Targets.read_impl context substitution ~trait:bound ~self_type:interface.for_type
              ~evidence:Bound
        in
        let receiver =
          match
            Types.find_implementing_receiver
              (Definitions.read_trait_interface context trait)
              (Definitions.read_impl_interface context implementing)
              trait_method
          with
          | Some receiver -> receiver
          | None -> trait_method.method_receiver
        in
        ( Lowered.Item.Generated
            (Any_entry
               {
                 impl = implementing;
                 name = trait_method.method_name;
                 receiver;
                 type_arguments = implementing_arguments;
               }),
          let signature, _, _ =
            Targets.make_any_entry_signature context ~any ~trait
              (Interface.Definition.read_method_signature context.lookups.interface ~owner:trait
                 trait_method)
          in
          signature ))
      slots
  in
  {
    table_item = item;
    capability = None;
    entries =
      Drop_and_copy.list_any_entries self_ty ~is_copyable:(Targets.is_copyable_any context any)
      @ entries;
  }

let lower context (generated : Lowered.Item.generated) : Emit_c.fragment =
  let item = Lowered.Item.Generated generated in
  match generated with
  | Entry impl_method -> build_entry context item impl_method
  | Any_entry impl_method -> build_any_entry context item impl_method
  | Locked_entry { capability; name } -> build_locked_entry context item ~capability ~name
  | Adapter { function_; instantiation; ty } ->
      build_adapter context item ~function_ ~instantiation ~ty
  | Program_main main -> build_program_main context item main
  | Test_main test -> build_test_main context item test

let lower_table context (table : Lowered.Item.table) : Lowered.table =
  let item = Lowered.Item.Table table in
  match table with
  | Impl_table { impl; type_arguments } -> build_impl_table context item ~impl ~type_arguments
  | Any_table { impl; type_arguments } -> build_any_table context item ~impl ~type_arguments
  | Locked_table capability -> build_locked_table context item ~capability
