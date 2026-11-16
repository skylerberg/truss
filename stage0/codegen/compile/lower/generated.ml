let make_generated_state context ~key ~definition ~substitution =
  Lowering.enter context
    ~builder:(Emit_c.Builder.create context.env ~key)
    (Lowering.make_frame
       (Definitions.make_unwritten_code ~definition ~substitution ~result:(Returns Types.unit)))

let choose_result_place st result_ty =
  match Lowering.find_result_place st with
  | Some place -> place
  | None -> Lowering.allocate_temporary st result_ty

let read_impl_capability context impl =
  let interface = Definitions.read_impl_interface context impl in
  (interface, interface.implements.trait, Definitions.list_evidence context [] interface.impl_uses)

let build_entry context (key : Instance.key) (impl_method : Instance.impl_method) :
    Emit_c.Builder.instance =
  let { Instance.impl; name; receiver; type_arguments } = impl_method in
  let path = Instance.make_method_path impl_method in
  let interface, capability, captured = read_impl_capability context impl in
  let _, capability_signature = Targets.lookup_capability_method context capability name in
  let _, result = Targets.make_entry_signature context capability_signature in
  let method_signature = Definitions.read_signature context path in
  let substitution = Definitions.bind method_signature.generics type_arguments in
  let st = make_generated_state context ~key ~definition:impl ~substitution in
  let builder = st.builder in
  let evidence = Emit_c.Builder.allocate_local builder ~name:"evidence" Convention.evidence in
  Lowering.set_result_slot st result;
  let parameter_places =
    List.map
      (fun (info : Types.parameter_info) ->
        let ty = Monomorphic.ground context.monomorphic substitution info.type_ in
        ( Lowering.allocate_parameter st ~owned:(info.mode = Own)
            (Monomorphic.ground_mode info.mode)
            ty,
          info.mode,
          ty ))
      capability_signature.parameters
  in
  Emit_c.Builder.start builder (Emit_c.Builder.allocate_block builder);
  let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
  let implementation =
    Emit_c.Builder.allocate_local builder (Pointer { target = Value self_ty; writable = true })
  in
  if not (Lowering.is_zero_size st self_ty) then
    Emit_c.Builder.emit builder
      (Call
         {
           target = Intrinsic Evidence_implementation;
           arguments = [ Copy (Lowered.make_local_place evidence) ];
           result = Returned (Lowered.make_local_place implementation);
         });
  st.evidence <-
    List.mapi
      (fun position capability ->
        let outer = Emit_c.Builder.allocate_local builder Convention.evidence in
        Emit_c.Builder.emit builder
          (Call
             {
               target = Intrinsic Evidence_outer;
               arguments =
                 [
                   Copy (Lowered.make_local_place evidence);
                   Constant (Integer (Int32, Z.of_int position));
                 ];
               result = Returned (Lowered.make_local_place outer);
             });
        (capability, Lowered.Copy (Lowered.make_local_place outer)))
      captured;
  let self_mode : Types.mode =
    match receiver with Mut -> Mut | Own -> Own | Read | Static -> Read
  in
  let result_ty =
    match capability_signature.output with
    | Returns ty -> Monomorphic.ground context.monomorphic [] ty
    | _ -> Definitions.raise_bug "a capability method that lends"
  in
  Targets.lower_instance_call st
    (Code { path; type_arguments })
    ~signature:method_signature ~substitution
    ~arguments:
      ((self_mode, self_ty, { Lowered.root = Local implementation; projections = [ Deref ] })
      :: List.map (fun ((_, place), mode, ty) -> (mode, ty, place)) parameter_places)
    ~destination:(choose_result_place st result_ty)
    ();
  Emit_c.Builder.build st.builder
    (Lowering.finish_function st
       ~returns:(capability_signature.output <> Returns Never)
       ~first:[ evidence ]
       ~rest:(List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places)
       ())

let build_locked_entry context (key : Instance.key) ~capability ~name : Emit_c.Builder.instance =
  let slot, capability_signature = Targets.lookup_capability_method context capability name in
  let c_signature, result = Targets.make_entry_signature context capability_signature in
  let st = make_generated_state context ~key ~definition:capability ~substitution:[] in
  let builder = st.builder in
  let evidence = Emit_c.Builder.allocate_local builder ~name:"evidence" Convention.evidence in
  Lowering.set_result_slot st result;
  let parameter_places =
    List.map
      (fun (info : Types.parameter_info) ->
        let ty = Monomorphic.ground context.monomorphic [] info.type_ in
        ( Lowering.allocate_parameter st ~owned:(info.mode = Own)
            (Monomorphic.ground_mode info.mode)
            ty,
          info.mode,
          ty ))
      capability_signature.parameters
  in
  Emit_c.Builder.start builder (Emit_c.Builder.allocate_block builder);
  let outer index : Lowered.operand =
    let outer = Emit_c.Builder.allocate_local builder Convention.evidence in
    Emit_c.Builder.emit builder
      (Call
         {
           target = Intrinsic Evidence_outer;
           arguments =
             [
               Copy (Lowered.make_local_place evidence); Constant (Integer (Int32, Z.of_int index));
             ];
           result = Returned (Lowered.make_local_place outer);
         });
    Copy (Lowered.make_local_place outer)
  in
  let implementation = outer 0 and tasks = outer 1 in
  let address = Emit_c.Builder.allocate_local builder (Raw (Pointer Opaque)) in
  Emit_c.Builder.emit builder
    (Call
       {
         target = Intrinsic Evidence_implementation;
         arguments = [ Copy (Lowered.make_local_place evidence) ];
         result = Returned (Lowered.make_local_place address);
       });
  let mutex =
    Lowered.make_local_place
      (Emit_c.Builder.allocate_local builder ~name:"mutex" (Value (Ground.make_builtin UInt64)))
  in
  Emit_c.Builder.emit builder
    (Assign (mutex, Convert (Copy (Lowered.make_local_place address), Integer UInt64)));
  let tasks_call name =
    let slot, signature =
      Targets.lookup_capability_method context (Well_known.make_path Tasks) name
    in
    Emit_c.Builder.emit builder
      (Call
         {
           target =
             Evidence_call
               {
                 evidence = tasks;
                 capability = Well_known.make_path Tasks;
                 slot;
                 signature = fst (Targets.make_entry_signature context signature);
               };
           arguments = [ Copy mutex ];
           result = Discarded;
         })
  in
  let result_ty =
    match capability_signature.output with
    | Returns ty -> Monomorphic.ground context.monomorphic [] ty
    | _ -> Definitions.raise_bug "a capability method that lends"
  in
  tasks_call "lock";
  Emit_c.Builder.emit builder
    (Call
       {
         target =
           Evidence_call { evidence = implementation; capability; slot; signature = c_signature };
         arguments =
           List.filter_map
             (fun ((_, place), mode, ty) -> Targets.pass st mode ty place)
             parameter_places;
         result = Convention.make_destination result (choose_result_place st result_ty);
       });
  tasks_call "unlock";
  Emit_c.Builder.build st.builder
    (Lowering.finish_function st
       ~returns:(capability_signature.output <> Returns Never)
       ~first:[ evidence ]
       ~rest:(List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places)
       ())

let build_locked_table (context : Definitions.context) (key : Instance.key) ~capability :
    Lowered.table =
  let interface = Definitions.read_trait_interface context capability in
  {
    table_key = key;
    capability = Some capability;
    entries =
      List.map
        (fun (trait_method : Types.trait_method) ->
          ( Instance.Generated (Locked_entry { capability; name = trait_method.method_name }),
            fst
              (Targets.make_entry_signature context
                 (Interface.Definition.read_method_signature context.lookups.interface
                    ~owner:capability trait_method)) ))
        interface.methods;
  }

let build_impl_table context (key : Instance.key) ~impl ~type_arguments : Lowered.table =
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
        ( Instance.Generated
            (Entry { impl; name = trait_method.method_name; receiver; type_arguments }),
          fst
            (Targets.make_entry_signature context
               (Interface.Definition.read_method_signature context.lookups.interface
                  ~owner:capability trait_method)) ))
      capability_interface.methods
  in
  { table_key = key; capability = Some capability; entries }

let find_real_implementation (interface : Interface.Lookups.t) (capability : Path.t) =
  match
    List.filter
      (function Path.Impl { module_; _ } -> Well_known.is_system_module module_ | _ -> false)
      (interface.names.impls_of_trait Path.standard_package capability)
  with
  | [] -> None
  | [ impl ] -> (
      match Interface.Definition.read_impl_interface interface impl with
      | Some impl_interface -> Some (impl, impl_interface)
      | None -> Definitions.raise_bug "the real implementation %s has no interface" (Path.show impl)
      )
  | impls ->
      Definitions.raise_bug "%s has %d real implementations: %s" (Path.show capability)
        (List.length impls)
        (String.concat ", " (List.map Path.show impls))

let list_real_implementations (st : Lowering.state) ~user capabilities =
  List.map
    (fun capability ->
      let impl, ty =
        match find_real_implementation st.context.lookups.interface capability with
        | Some (impl, impl_interface) ->
            (impl, Monomorphic.ground st.context.monomorphic [] impl_interface.for_type)
        | None ->
            Lowering.raise_unsupported "%s uses %s, which has no real implementation" user
              (Ground.show_path_name capability)
      in
      let implementation =
        if Lowering.is_zero_size st ty then Lowered.Constant Null
        else begin
          let value = Lowering.allocate_binding st ty in
          let constructor : Path.t =
            match ty with
            | Named { path; _ } -> Method { owner = path; name = "new"; receiver = Static }
            | _ ->
                Definitions.raise_bug "%s implements %s" (Ground.to_string ty)
                  (Path.show capability)
          in
          Targets.lower_instance_call st
            (Code { path = constructor; type_arguments = [] })
            ~signature:(Definitions.read_signature st.context constructor)
            ~substitution:[] ~arguments:[] ~destination:value ();
          Address { place = value; writable = true }
        end
      in
      (capability, Targets.lower_implementation_evidence st ~impl ~type_arguments:[] ~implementation))
    capabilities

let text_copied_from = Well_known.make_path Text_copied_from

let build_program_main context (key : Instance.key) main_path : Emit_c.Builder.instance =
  let st = make_generated_state context ~key ~definition:main_path ~substitution:[] in
  let builder = st.builder in
  let count = Emit_c.Builder.allocate_local builder ~name:"count" (Raw (Integer Int32)) in
  let arguments_pointer =
    Emit_c.Builder.allocate_local builder ~name:"arguments" (Raw (Pointer Opaque))
  in
  Lowering.set_result_slot st (Returned (Raw (Integer Int32)));
  Emit_c.Builder.start builder (Emit_c.Builder.allocate_block builder);
  let signature = Definitions.read_signature context main_path in
  let list_ty, list_mode =
    match signature.parameters with
    | [ info ] -> (Monomorphic.ground context.monomorphic [] info.type_, info.mode)
    | _ -> Definitions.raise_bug "main takes its arguments"
  in
  let storage_field, _, string_ty = Targets.list_parts context.monomorphic list_ty in
  let list = Lowering.allocate_temporary st list_ty in
  let lower operation type_arguments arguments destination =
    ignore
      (Intrinsics.lower ~checks:context.checks context.env builder context.types operation
         ~type_arguments arguments ~destination
         ~site:{ definition = main_path; offset = 0 })
  in
  let wanted = Emit_c.Builder.allocate_local builder (Value context.types.uint64) in
  Emit_c.Builder.emit builder
    (Assign
       ( Lowered.make_local_place wanted,
         Convert (Copy (Lowered.make_local_place count), Integer UInt64) ));
  lower Storage_with_capacity [ string_ty ]
    [ Value (Copy (Lowered.make_local_place wanted)) ]
    (Some (Lowered.project list (Field storage_field)));
  Emit_c.Builder.emit_loop builder ~integer:Int32
    ~count:(Copy (Lowered.make_local_place count))
    (fun index ->
      let length = Emit_c.Builder.allocate_local builder (Value context.types.uint64)
      and bytes = Emit_c.Builder.allocate_local builder (Raw (Pointer Opaque)) in
      let call intrinsic arguments result =
        Emit_c.Builder.emit builder
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
      let view = Lowering.allocate_temporary st view_ty in
      Emit_c.Builder.emit builder
        (Assign
           ( view,
             Storage.build_view view_ty
               ~elements:(Copy (Lowered.make_local_place bytes))
               ~length:(Copy (Lowered.make_local_place length)) ));
      let text = Lowering.allocate_temporary st string_ty in
      Targets.lower_instance_call st
        (Code { path = text_copied_from; type_arguments = [] })
        ~signature:(Definitions.read_signature context text_copied_from)
        ~substitution:[]
        ~arguments:[ (Read, view_ty, view) ]
        ~destination:text ();
      lower Storage_push [ string_ty ]
        [ Place (Lowered.project list (Field storage_field)); Value (Lowering.move_place st text) ]
        None);
  st.evidence <-
    list_real_implementations st ~user:"main"
      (Definitions.list_evidence st.context [] signature.uses);
  let exit_ty =
    match signature.output with
    | Returns ty -> Monomorphic.ground context.monomorphic [] ty
    | _ -> Definitions.raise_bug "main lends"
  in
  let exit = Lowering.allocate_temporary st exit_ty in
  Targets.lower_instance_call st
    (Code { path = main_path; type_arguments = [] })
    ~signature ~substitution:[]
    ~arguments:[ (list_mode, list_ty, list) ]
    ~destination:exit ();
  (match (Monomorphic.compute_shape context.monomorphic exit_ty, Lowering.find_result_place st) with
  | Record [ (field, _) ], Some status ->
      Emit_c.Builder.emit builder
        (Assign (status, Convert (Copy (Lowered.project exit (Field field)), Integer Int32)))
  | _ -> Definitions.raise_bug "an ExitCode that is not a record of one field");
  Emit_c.Builder.build st.builder
    (Lowering.finish_function st ~first:[ count; arguments_pointer ] ~rest:[] ())

let build_adapter context (key : Instance.key) ~(function_ : Path.t) ~type_arguments
    ~(ty : Ground.function_type) : Emit_c.Builder.instance =
  let signature = Definitions.read_signature context function_ in
  let substitution = Definitions.bind signature.generics type_arguments in
  let st = make_generated_state context ~key ~definition:function_ ~substitution in
  let builder = st.builder in
  let environment =
    Emit_c.Builder.allocate_local builder ~name:"environment" (Raw (Nullable_pointer Opaque))
  in
  Lowering.set_result_slot st (Convention.classify_result context.env ty.result);
  let parameter_places =
    List.map
      (fun ((mode : Ground.mode), ty) ->
        let types_mode : Types.mode = match mode with Read -> Read | Mut -> Mut | Own -> Own in
        (Lowering.allocate_parameter st ~owned:(mode = Own) mode ty, types_mode, ty))
      ty.parameters
  in
  let evidence = Lowering.list_evidence_parameters st ty.uses in
  Emit_c.Builder.start builder (Emit_c.Builder.allocate_block builder);
  Targets.lower_instance_call st
    (Code { path = function_; type_arguments })
    ~signature ~substitution
    ~arguments:(List.map (fun ((_, place), mode, ty) -> (mode, ty, place)) parameter_places)
    ~destination:(choose_result_place st ty.result)
    ();
  Emit_c.Builder.build st.builder
    (Lowering.finish_function st ~returns:(ty.result <> Never) ~first:[ environment ]
       ~rest:(List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places @ evidence)
       ())

let build_any_entry context (key : Instance.key) (impl_method : Instance.impl_method) :
    Emit_c.Builder.instance =
  let { Instance.impl; name; receiver; type_arguments } = impl_method in
  let path = Instance.make_method_path impl_method in
  let interface = Definitions.read_impl_interface context impl in
  let trait = interface.implements.trait in
  let _, trait_signature = Targets.lookup_dynamic_method context trait name receiver in
  let method_signature = Definitions.read_signature context path in
  let substitution = Definitions.bind method_signature.generics type_arguments in
  let any = Types.substitute_trait substitution interface.implements in
  let _, result, capabilities =
    Targets.make_any_entry_signature context ~any ~trait trait_signature
  in
  let st = make_generated_state context ~key ~definition:impl ~substitution in
  let builder = st.builder in
  let value = Emit_c.Builder.allocate_local builder ~name:"value" (Raw (Pointer Opaque)) in
  Lowering.set_result_slot st result;
  let parameter_places =
    List.map
      (fun (info : Types.parameter_info) ->
        let ty = Monomorphic.ground context.monomorphic substitution info.type_ in
        ( Lowering.allocate_parameter st ~owned:(info.mode = Own)
            (Monomorphic.ground_mode info.mode)
            ty,
          info.mode,
          ty ))
      method_signature.parameters
  in
  let evidence = Lowering.list_evidence_parameters st capabilities in
  let lending =
    List.map
      (fun ty -> Emit_c.Builder.allocate_local builder ~name:"lend" ty)
      (Definitions.list_lending_parameters context substitution method_signature.output)
  in
  Emit_c.Builder.start builder (Emit_c.Builder.allocate_block builder);
  let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
  let typed =
    Emit_c.Builder.allocate_local builder (Pointer { target = Value self_ty; writable = true })
  in
  if not (Lowering.is_zero_size st self_ty) then
    Emit_c.Builder.emit builder
      (Assign (Lowered.make_local_place typed, Use (Copy (Lowered.make_local_place value))));
  let self_mode : Types.mode =
    match receiver with Mut -> Mut | Own -> Own | Read | Static -> Read
  in
  let destination =
    match (method_signature.output, Lowering.find_result_place st) with
    | _, Some place -> place
    | Returns result_type, None ->
        Lowering.allocate_temporary st
          (Monomorphic.ground context.monomorphic substitution result_type)
    | Lends _, None -> Lowering.allocate_temporary st (Ground.make_builtin Unit)
  in
  Targets.lower_instance_call st
    (Code { path; type_arguments })
    ~signature:method_signature ~substitution
    ~arguments:
      ((self_mode, self_ty, { Lowered.root = Local typed; projections = [ Deref ] })
      :: List.map (fun ((_, place), mode, ty) -> (mode, ty, place)) parameter_places)
    ~lending:(List.map (fun local -> Lowered.Copy (Lowered.make_local_place local)) lending)
    ~destination ();
  Emit_c.Builder.build st.builder
    (Lowering.finish_function st
       ~returns:(method_signature.output <> Returns Never)
       ~first:[ value ]
       ~rest:
         (List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places
         @ evidence @ lending)
       ())

let build_any_table context (key : Instance.key) ~impl ~type_arguments : Lowered.table =
  let interface = Definitions.read_impl_interface context impl in
  let trait = interface.implements.trait in
  let substitution = Definitions.bind interface.impl_generics type_arguments in
  let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
  let any = Types.substitute_trait substitution interface.implements in
  let trait_interface = Definitions.read_trait_interface context trait in
  let entries =
    List.map
      (fun (trait_method : Types.trait_method) ->
        let receiver =
          match Types.find_implementing_receiver trait_interface interface trait_method with
          | Some receiver -> receiver
          | None -> trait_method.method_receiver
        in
        ( Instance.Generated
            (Any_entry { impl; name = trait_method.method_name; receiver; type_arguments }),
          let signature, _, _ =
            Targets.make_any_entry_signature context ~any ~trait
              (Interface.Definition.read_method_signature context.lookups.interface ~owner:trait
                 trait_method)
          in
          signature ))
      (Targets.list_any_methods context trait)
  in
  {
    table_key = key;
    capability = None;
    entries =
      Drop_and_copy.list_any_entries self_ty ~is_copyable:(Targets.is_copyable_any context any)
      @ entries;
  }

let lower context (generated : Instance.generated) : Emit_c.Builder.instance =
  let key = Instance.Generated generated in
  match generated with
  | Entry impl_method -> build_entry context key impl_method
  | Any_entry impl_method -> build_any_entry context key impl_method
  | Locked_entry { capability; name } -> build_locked_entry context key ~capability ~name
  | Adapter { function_; type_arguments; ty } ->
      build_adapter context key ~function_ ~type_arguments ~ty
  | Program_main main -> build_program_main context key main

let lower_table context (table : Instance.table) : Lowered.table =
  let key = Instance.Table table in
  match table with
  | Impl_table { impl; type_arguments } -> build_impl_table context key ~impl ~type_arguments
  | Any_table { impl; type_arguments } -> build_any_table context key ~impl ~type_arguments
  | Locked_table capability -> build_locked_table context key ~capability
