open Definitions
open Lowering
open Targets
open Emit_c.Builder

let generated_state context ~key ~definition ~substitution =
  enter context ~builder:(create context.env ~key)
    (frame_of (unwritten ~definition ~substitution ~result:(Returns Types.unit)))

let passed_on st result_ty =
  match result_place st with Some place -> place | None -> temporary st result_ty

let impl_capability context impl =
  let interface = impl_interface context impl in
  (interface, interface.implements.trait, evidence_for context [] interface.impl_uses)

let entry context (key : Instance.key) (impl_method : Instance.impl_method) :
    Emit_c.Builder.instance =
  let { Instance.impl; name; receiver; type_arguments } = impl_method in
  let path = Instance.make_method_path impl_method in
  let interface, capability, captured = impl_capability context impl in
  let _, capability_signature = capability_method context capability name in
  let _, result = entry_signature context capability_signature in
  let method_signature = signature_of context path in
  let substitution = bind method_signature.generics type_arguments in
  let st = generated_state context ~key ~definition:impl ~substitution in
  let builder = st.builder in
  let evidence = local builder ~name:"evidence" Convention.evidence in
  result_slot st result;
  let parameter_places =
    List.map
      (fun (info : Types.parameter_info) ->
        let ty = Monomorphic.ground context.monomorphic substitution info.type_ in
        (parameter st ~owned:(info.mode = Own) (Monomorphic.mode info.mode) ty, info.mode, ty))
      capability_signature.parameters
  in
  start builder (block builder);
  let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
  let implementation = local builder (Pointer { target = Value self_ty; writable = true }) in
  if not (is_zero_size st self_ty) then
    emit builder
      (Call
         {
           target = Intrinsic Evidence_implementation;
           arguments = [ Copy (at evidence) ];
           result = Returned (at implementation);
         });
  st.evidence <-
    List.mapi
      (fun position capability ->
        let outer = local builder Convention.evidence in
        emit builder
          (Call
             {
               target = Intrinsic Evidence_outer;
               arguments = [ Copy (at evidence); Constant (Integer (Int32, Z.of_int position)) ];
               result = Returned (at outer);
             });
        (capability, Lowered.Copy (at outer)))
      captured;
  let self_mode : Types.mode =
    match receiver with Mut -> Mut | Own -> Own | Read | Static -> Read
  in
  let result_ty =
    match capability_signature.output with
    | Returns ty -> Monomorphic.ground context.monomorphic [] ty
    | _ -> bug "a capability method that lends"
  in
  call_instance st
    (Code { path; type_arguments })
    ~signature:method_signature ~substitution
    ~arguments:
      ((self_mode, self_ty, { Lowered.root = Local implementation; projections = [ Deref ] })
      :: List.map (fun ((_, place), mode, ty) -> (mode, ty, place)) parameter_places)
    ~destination:(passed_on st result_ty) ();
  finish_function st
    ~returns:(capability_signature.output <> Returns Never)
    ~first:[ evidence ]
    ~rest:(List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places)
    ();
  built st.builder

let locked_entry context (key : Instance.key) ~capability ~name : Emit_c.Builder.instance =
  let slot, capability_signature = capability_method context capability name in
  let c_signature, result = entry_signature context capability_signature in
  let st = generated_state context ~key ~definition:capability ~substitution:[] in
  let builder = st.builder in
  let evidence = local builder ~name:"evidence" Convention.evidence in
  result_slot st result;
  let parameter_places =
    List.map
      (fun (info : Types.parameter_info) ->
        let ty = Monomorphic.ground context.monomorphic [] info.type_ in
        (parameter st ~owned:(info.mode = Own) (Monomorphic.mode info.mode) ty, info.mode, ty))
      capability_signature.parameters
  in
  start builder (block builder);
  let outer index : Lowered.operand =
    let outer = local builder Convention.evidence in
    emit builder
      (Call
         {
           target = Intrinsic Evidence_outer;
           arguments = [ Copy (at evidence); Constant (Integer (Int32, Z.of_int index)) ];
           result = Returned (at outer);
         });
    Copy (at outer)
  in
  let implementation = outer 0 and tasks = outer 1 in
  let address = local builder (Raw (Pointer Opaque)) in
  emit builder
    (Call
       {
         target = Intrinsic Evidence_implementation;
         arguments = [ Copy (at evidence) ];
         result = Returned (at address);
       });
  let mutex = at (local builder ~name:"mutex" (Value (Ground.builtin UInt64))) in
  emit builder (Assign (mutex, Convert (Copy (at address), Integer UInt64)));
  let tasks_call name =
    let slot, signature = capability_method context (Well_known.path Tasks) name in
    emit builder
      (Call
         {
           target =
             Evidence_call
               {
                 evidence = tasks;
                 capability = Well_known.path Tasks;
                 slot;
                 signature = fst (entry_signature context signature);
               };
           arguments = [ Copy mutex ];
           result = Discarded;
         })
  in
  let result_ty =
    match capability_signature.output with
    | Returns ty -> Monomorphic.ground context.monomorphic [] ty
    | _ -> bug "a capability method that lends"
  in
  tasks_call "lock";
  emit builder
    (Call
       {
         target =
           Evidence_call { evidence = implementation; capability; slot; signature = c_signature };
         arguments =
           List.filter_map (fun ((_, place), mode, ty) -> pass st mode ty place) parameter_places;
         result = Convention.destination result (passed_on st result_ty);
       });
  tasks_call "unlock";
  finish_function st
    ~returns:(capability_signature.output <> Returns Never)
    ~first:[ evidence ]
    ~rest:(List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places)
    ();
  built st.builder

let locked_table context (key : Instance.key) ~capability : Lowered.table =
  let interface =
    match Interface.Definition.read_trait_interface context.lookups.interface capability with
    | Some interface -> interface
    | None -> bug "no interface for %s" (Path.show capability)
  in
  {
    table_key = key;
    capability = Some capability;
    entries =
      List.map
        (fun (trait_method : Types.trait_method) ->
          ( Instance.Generated (Locked_entry { capability; name = trait_method.method_name }),
            fst
              (entry_signature context
                 (Interface.Definition.read_method_signature context.lookups.interface
                    ~owner:capability trait_method)) ))
        interface.methods;
  }

let impl_table context (key : Instance.key) ~impl ~type_arguments : Lowered.table =
  let interface, capability, _ = impl_capability context impl in
  let capability_interface =
    match Interface.Definition.read_trait_interface context.lookups.interface capability with
    | Some position -> position
    | None -> bug "no interface for %s" (Path.show capability)
  in
  let entries =
    List.map
      (fun (trait_method : Types.trait_method) ->
        let receiver =
          match
            List.find_opt (fun (name, _) -> name = trait_method.method_name) interface.impl_methods
          with
          | Some (_, receiver) -> receiver
          | None -> bug "%s does not write %s" (Path.show impl) trait_method.method_name
        in
        ( Instance.Generated
            (Entry { impl; name = trait_method.method_name; receiver; type_arguments }),
          fst
            (entry_signature context
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
      | None -> bug "the real implementation %s has no interface" (Path.show impl))
  | impls ->
      bug "%s has %d real implementations: %s" (Path.show capability) (List.length impls)
        (String.concat ", " (List.map Path.show impls))

let real_implementations st ~user capabilities =
  List.map
    (fun capability ->
      let impl, ty =
        match find_real_implementation st.context.lookups.interface capability with
        | Some (impl, impl_interface) ->
            (impl, Monomorphic.ground st.context.monomorphic [] impl_interface.for_type)
        | None ->
            unsupported "%s uses %s, which has no real implementation" user
              (Ground.path_name capability)
      in
      let implementation =
        if is_zero_size st ty then Lowered.Constant Null
        else begin
          let value = binding st ty in
          let constructor : Path.t =
            match ty with
            | Named { path; _ } -> Method { owner = path; name = "new"; receiver = Static }
            | _ -> bug "%s implements %s" (Ground.to_string ty) (Path.show capability)
          in
          call_instance st
            (Code { path = constructor; type_arguments = [] })
            ~signature:(signature_of st.context constructor)
            ~substitution:[] ~arguments:[] ~destination:value ();
          Address { place = value; writable = true }
        end
      in
      (capability, implementation_evidence st ~impl ~type_arguments:[] ~implementation))
    capabilities

let text_copied_from = Well_known.path Text_copied_from

let program_main context (key : Instance.key) main_path : Emit_c.Builder.instance =
  let st = generated_state context ~key ~definition:main_path ~substitution:[] in
  let builder = st.builder in
  let count = local builder ~name:"count" (Raw (Integer Int32)) in
  let arguments_pointer = local builder ~name:"arguments" (Raw (Pointer Opaque)) in
  result_slot st (Returned (Raw (Integer Int32)));
  start builder (block builder);
  let signature = signature_of context main_path in
  let list_ty, list_mode =
    match signature.parameters with
    | [ info ] -> (Monomorphic.ground context.monomorphic [] info.type_, info.mode)
    | _ -> bug "main takes its arguments"
  in
  let storage_field, _, string_ty = list_parts context.monomorphic list_ty in
  let list = temporary st list_ty in
  let lower operation type_arguments arguments destination =
    ignore
      (Intrinsics.lower ~checks:context.checks context.env builder context.types operation
         ~type_arguments arguments ~destination
         ~site:{ definition = main_path; offset = 0 })
  in
  let wanted = local builder (Value context.types.uint64) in
  emit builder (Assign (at wanted, Convert (Copy (at count), Integer UInt64)));
  lower Storage_with_capacity [ string_ty ]
    [ Value (Copy (at wanted)) ]
    (Some (list / Field storage_field));
  loop builder ~integer:Int32
    ~count:(Copy (at count))
    (fun index ->
      let length = local builder (Value context.types.uint64)
      and bytes = local builder (Raw (Pointer Opaque)) in
      let call intrinsic arguments result =
        emit builder
          (Call { target = Intrinsic intrinsic; arguments; result = Returned (at result) })
      in
      call Program_argument [ Copy (at arguments_pointer); Copy (at index) ] bytes;
      call Terminated_length [ Copy (at bytes) ] length;
      let view_ty = Storage.make_view_type (Ground.builtin UInt8) in
      let view = temporary st view_ty in
      emit builder
        (Assign
           (view, Storage.build_view view_ty ~elements:(Copy (at bytes)) ~length:(Copy (at length))));
      let text = temporary st string_ty in
      call_instance st
        (Code { path = text_copied_from; type_arguments = [] })
        ~signature:(signature_of context text_copied_from)
        ~substitution:[]
        ~arguments:[ (Read, view_ty, view) ]
        ~destination:text ();
      lower Storage_push [ string_ty ]
        [ Place (list / Field storage_field); Value (moved st text) ]
        None);
  st.evidence <- real_implementations st ~user:"main" (evidence_for st.context [] signature.uses);
  let exit_ty =
    match signature.output with
    | Returns ty -> Monomorphic.ground context.monomorphic [] ty
    | _ -> bug "main lends"
  in
  let exit = temporary st exit_ty in
  call_instance st
    (Code { path = main_path; type_arguments = [] })
    ~signature ~substitution:[]
    ~arguments:[ (list_mode, list_ty, list) ]
    ~destination:exit ();
  (match (Monomorphic.shape context.monomorphic exit_ty, result_place st) with
  | Record [ (field, _) ], Some status ->
      emit builder (Assign (status, Convert (Copy (exit / Field field), Integer Int32)))
  | _ -> bug "an ExitCode that is not a record of one field");
  finish_function st ~first:[ count; arguments_pointer ] ~rest:[] ();
  built st.builder

let adapter context (key : Instance.key) ~(function_ : Path.t) ~type_arguments
    ~(ty : Ground.function_type) : Emit_c.Builder.instance =
  let signature = signature_of context function_ in
  let substitution = bind signature.generics type_arguments in
  let st = generated_state context ~key ~definition:function_ ~substitution in
  let builder = st.builder in
  let environment = local builder ~name:"environment" (Raw (Nullable_pointer Opaque)) in
  result_slot st (Convention.result context.env ty.result);
  let parameter_places =
    List.map
      (fun ((mode : Ground.mode), ty) ->
        let types_mode : Types.mode = match mode with Read -> Read | Mut -> Mut | Own -> Own in
        (parameter st ~owned:(mode = Own) mode ty, types_mode, ty))
      ty.parameters
  in
  let evidence = evidence_parameters st ty.uses in
  start builder (block builder);
  call_instance st
    (Code { path = function_; type_arguments })
    ~signature ~substitution
    ~arguments:(List.map (fun ((_, place), mode, ty) -> (mode, ty, place)) parameter_places)
    ~destination:(passed_on st ty.result) ();
  finish_function st ~returns:(ty.result <> Never) ~first:[ environment ]
    ~rest:(List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places @ evidence)
    ();
  built st.builder

let any_entry context (key : Instance.key) (impl_method : Instance.impl_method) :
    Emit_c.Builder.instance =
  let { Instance.impl; name; receiver; type_arguments } = impl_method in
  let path = Instance.make_method_path impl_method in
  let interface = impl_interface context impl in
  let trait = interface.implements.trait in
  let _, trait_signature = dynamic_method context trait name in
  let method_signature = signature_of context path in
  let substitution = bind method_signature.generics type_arguments in
  let any = Types.substitute_trait substitution interface.implements in
  let _, result, capabilities = any_entry_signature context ~any ~trait trait_signature in
  let st = generated_state context ~key ~definition:impl ~substitution in
  let builder = st.builder in
  let value = local builder ~name:"value" (Raw (Pointer Opaque)) in
  result_slot st result;
  let parameter_places =
    List.map
      (fun (info : Types.parameter_info) ->
        let ty = Monomorphic.ground context.monomorphic substitution info.type_ in
        (parameter st ~owned:(info.mode = Own) (Monomorphic.mode info.mode) ty, info.mode, ty))
      method_signature.parameters
  in
  let evidence = evidence_parameters st capabilities in
  let lending =
    List.map
      (fun ty -> local builder ~name:"lend" ty)
      (lending_parameters context substitution method_signature.output)
  in
  start builder (block builder);
  let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
  let typed = local builder (Pointer { target = Value self_ty; writable = true }) in
  if not (is_zero_size st self_ty) then emit builder (Assign (at typed, Use (Copy (at value))));
  let self_mode : Types.mode =
    match receiver with Mut -> Mut | Own -> Own | Read | Static -> Read
  in
  let destination =
    match (method_signature.output, result_place st) with
    | _, Some place -> place
    | Returns result_type, None ->
        temporary st (Monomorphic.ground context.monomorphic substitution result_type)
    | Lends _, None -> temporary st (Ground.builtin Unit)
  in
  call_instance st
    (Code { path; type_arguments })
    ~signature:method_signature ~substitution
    ~arguments:
      ((self_mode, self_ty, { Lowered.root = Local typed; projections = [ Deref ] })
      :: List.map (fun ((_, place), mode, ty) -> (mode, ty, place)) parameter_places)
    ~lending:(List.map (fun local -> Lowered.Copy (at local)) lending)
    ~destination ();
  finish_function st
    ~returns:(method_signature.output <> Returns Never)
    ~first:[ value ]
    ~rest:
      (List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places @ evidence @ lending)
    ();
  built st.builder

let any_table context (key : Instance.key) ~impl ~type_arguments : Lowered.table =
  let interface = impl_interface context impl in
  let trait = interface.implements.trait in
  let substitution = bind interface.impl_generics type_arguments in
  let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
  let any = Types.substitute_trait substitution interface.implements in
  let entries =
    List.map
      (fun (trait_method : Types.trait_method) ->
        let receiver =
          match
            List.find_opt (fun (name, _) -> name = trait_method.method_name) interface.impl_methods
          with
          | Some (_, receiver) -> receiver
          | None -> trait_method.method_receiver
        in
        ( Instance.Generated
            (Any_entry { impl; name = trait_method.method_name; receiver; type_arguments }),
          let signature, _, _ =
            any_entry_signature context ~any ~trait
              (Interface.Definition.read_method_signature context.lookups.interface ~owner:trait
                 trait_method)
          in
          signature ))
      (any_methods context trait)
  in
  {
    table_key = key;
    capability = None;
    entries = Drop_and_copy.any_entries self_ty ~is_copyable:(is_copyable_any context any) @ entries;
  }

let lower context (generated : Instance.generated) : Emit_c.Builder.instance =
  let key = Instance.Generated generated in
  match generated with
  | Entry impl_method -> entry context key impl_method
  | Any_entry impl_method -> any_entry context key impl_method
  | Locked_entry { capability; name } -> locked_entry context key ~capability ~name
  | Adapter { function_; type_arguments; ty } -> adapter context key ~function_ ~type_arguments ~ty
  | Program_main main -> program_main context key main

let lower_table context (table : Instance.table) : Lowered.table =
  let key = Instance.Table table in
  match table with
  | Impl_table { impl; type_arguments } -> impl_table context key ~impl ~type_arguments
  | Any_table { impl; type_arguments } -> any_table context key ~impl ~type_arguments
  | Locked_table capability -> locked_table context key ~capability
