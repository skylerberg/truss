(* Instances lowering makes rather than finds in source: capability
   entries and tables, the real implementations' evidence, the program's
   main, adapters, and [any] entries and tables. *)

open Definitions
open Lowering
open Targets
open Lir_builder

let generated_state context ~anchor ~substitution =
  enter context
    (frame_of ~inlined:[]
       (unwritten
          ~definition_key:
            {
              Names.module_ = { package = { owner = None; name = "" }; modules = [] };
              path = anchor;
              ordinal = 0;
            }
          ~anchor ~substitution ~result:(Returns Types.unit)))

(* Where a generated function's result goes when it is another function's,
   passed on as it came: the slot, or a local for a result of no size. *)
let passed_on st result_ty =
  match result_place st with Some place -> place | None -> temporary st result_ty

(* The capability an [impl] implements, and the capabilities its own
   methods use, in path order, which its evidence captures. *)
let impl_capability context impl =
  let interface = impl_interface context impl in
  (interface, interface.implements.trait, evidence_for context [] interface.impl_uses)

(* An entry: unpacks the implementation and the evidence it captured from
   the evidence it is called with, and calls the [impl]'s method. *)
let entry context (key : Instance.key) (method_key : Instance.key) : Lir.t =
  let path, type_arguments =
    match method_key with
    | Code { path; type_arguments } -> (path, type_arguments)
    | _ -> bug "an entry's method"
  in
  let impl, name, receiver =
    match path with
    | Method { owner; name; receiver } -> (owner, name, receiver)
    | _ -> bug "an entry for a function"
  in
  let interface, capability, captured = impl_capability context impl in
  let _, capability_signature = capability_method context capability name in
  let _, result = entry_signature context capability_signature in
  let method_signature = signature_of context path in
  let substitution = bind method_signature.generics type_arguments in
  let st = generated_state context ~anchor:impl ~substitution in
  let b = st.b in
  let evidence = local b ~name:"evidence" Convention.evidence in
  result_slot st result;
  let parameter_places =
    List.map
      (fun (info : Types.parameter_info) ->
        let ty = Monomorphic.ground context.monomorphic substitution info.type_ in
        (parameter st ~owned:(info.mode = Own) (Monomorphic.mode info.mode) ty, info.mode, ty))
      capability_signature.parameters
  in
  start b (block b);
  let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
  let implementation = local b (Pointer { target = Value self_ty; writable = true }) in
  if not (is_zero_size st self_ty) then
    emit b
      (Call
         {
           target = Intrinsic Evidence_implementation;
           arguments = [ Copy (at evidence) ];
           result = Returned (at implementation);
         });
  st.evidence <-
    List.mapi
      (fun i capability ->
        let outer = local b Convention.evidence in
        emit b
          (Call
             {
               target = Intrinsic Evidence_outer;
               arguments = [ Copy (at evidence); Constant (Integer (Int32, Z.of_int i)) ];
               result = Returned (at outer);
             });
        (capability, Lir.Copy (at outer)))
      captured;
  let self_mode : Types.mode =
    match receiver with Mut -> Mut | Own -> Own | Read | Static -> Read
  in
  let result_ty =
    match capability_signature.output with
    | Returns ty -> Monomorphic.ground context.monomorphic [] ty
    | _ -> bug "a capability method that yields"
  in
  call_instance st method_key ~signature:method_signature ~substitution
    ~arguments:
      ((self_mode, self_ty, { Lir.root = Local implementation; projections = [ Deref ] })
      :: List.map (fun ((_, place), mode, ty) -> (mode, ty, place)) parameter_places)
    ~destination:(passed_on st result_ty) ();
  {
    key;
    main =
      finish_function st
        ~returns:(capability_signature.output <> Returns Never)
        ~first:[ evidence ]
        ~rest:(List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places)
        ();
    nested = [||];
  }

(* The entry of a capability's locking table for the method [name]. The
   evidence it is called with was built by a [provide mut] whose body can
   use [Tasks]: its implementation pointer is the address of the mutex,
   its first outer evidence is the implementation's own evidence, and its
   second is the evidence for [Tasks]. The entry locks the mutex, calls
   the implementation's entry, and unlocks the mutex, so calls of one
   implementation by several tasks are mutually exclusive. *)
let locked_entry context (key : Instance.key) ~capability ~name : Lir.t =
  let slot, capability_signature = capability_method context capability name in
  let lir_signature, result = entry_signature context capability_signature in
  let st = generated_state context ~anchor:capability ~substitution:[] in
  let b = st.b in
  let evidence = local b ~name:"evidence" Convention.evidence in
  result_slot st result;
  let parameter_places =
    List.map
      (fun (info : Types.parameter_info) ->
        let ty = Monomorphic.ground context.monomorphic [] info.type_ in
        (parameter st ~owned:(info.mode = Own) (Monomorphic.mode info.mode) ty, info.mode, ty))
      capability_signature.parameters
  in
  start b (block b);
  let outer index : Lir.operand =
    let outer = local b Convention.evidence in
    emit b
      (Call
         {
           target = Intrinsic Evidence_outer;
           arguments = [ Copy (at evidence); Constant (Integer (Int32, Z.of_int index)) ];
           result = Returned (at outer);
         });
    Copy (at outer)
  in
  let implementation = outer 0 and tasks = outer 1 in
  let address = local b (Raw (Pointer Opaque)) in
  emit b
    (Call
       {
         target = Intrinsic Evidence_implementation;
         arguments = [ Copy (at evidence) ];
         result = Returned (at address);
       });
  let mutex = at (local b ~name:"mutex" (Value (Monomorphic.builtin UInt64))) in
  emit b (Assign (mutex, Convert (Copy (at address), Integer UInt64)));
  let tasks_call name =
    let slot, signature = capability_method context Core_walk.tasks_capability name in
    emit b
      (Call
         {
           target =
             Evidence_call
               {
                 evidence = tasks;
                 capability = Core_walk.tasks_capability;
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
    | _ -> bug "a capability method that yields"
  in
  tasks_call "lock";
  emit b
    (Call
       {
         target =
           Evidence_call { evidence = implementation; capability; slot; signature = lir_signature };
         arguments =
           List.filter_map (fun ((_, place), mode, ty) -> pass st mode ty place) parameter_places;
         result = Convention.destination result (passed_on st result_ty);
       });
  tasks_call "unlock";
  {
    key;
    main =
      finish_function st
        ~returns:(capability_signature.output <> Returns Never)
        ~first:[ evidence ]
        ~rest:(List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places)
        ();
    nested = [||];
  }

(* A capability's locking table: a locking entry for each of the
   capability's methods, in the capability's order. *)
let locked_table context (key : Instance.key) ~capability : Lir.table =
  let interface =
    match demand context Environment.trait_interface capability with
    | Some interface -> interface
    | None -> bug "no interface for %s" (Path.show capability)
  in
  {
    table_key = key;
    capability = Some capability;
    entries =
      List.map
        (fun (m : Types.trait_method) ->
          ( Instance.Locked_entry { capability; name = m.method_name },
            fst (entry_signature context m.method_signature) ))
        interface.methods;
  }

(* A capability [impl]'s table: an entry for each of the capability's
   methods, in the capability's order. *)
let table context (key : Instance.key) : Lir.table =
  match key with
  | Table { impl; type_arguments } ->
      let interface, capability, _ = impl_capability context impl in
      let capability_interface =
        match demand context Environment.trait_interface capability with
        | Some i -> i
        | None -> bug "no interface for %s" (Path.show capability)
      in
      let entries =
        List.map
          (fun (m : Types.trait_method) ->
            let receiver =
              match
                List.find_opt (fun (name, _, _) -> name = m.method_name) interface.impl_methods
              with
              | Some (_, receiver, _) -> receiver
              | None -> bug "%s does not write %s" (Path.show impl) m.method_name
            in
            let method_key =
              Instance.Code
                { path = Method { owner = impl; name = m.method_name; receiver }; type_arguments }
            in
            (Instance.Entry method_key, fst (entry_signature context m.method_signature)))
          capability_interface.methods
      in
      { table_key = key; capability = Some capability; entries }
  | _ -> bug "not a table: %s" (Instance.to_string key)

(* The [impl] of a standard capability by its real implementation: the
   standard library's [System] type for it, such as [SystemConsole], in the
   module of [standard::system] named for the capability, as [FileRead]'s is
   in [standard::system::file_read]. *)
let real_implementation (capability : Path.t) : Path.t =
  let name = Ground.path_name capability in
  let module_name =
    String.concat ""
      (List.mapi
         (fun index letter ->
           let lower = String.make 1 (Char.lowercase_ascii letter) in
           if index > 0 && Char.uppercase_ascii letter = letter then "_" ^ lower else lower)
         (List.of_seq (String.to_seq name)))
  in
  Impl
    {
      module_ = Well_known.system_module module_name;
      trait = name;
      for_type = { type_name = "System" ^ name; generics = [] };
    }

(* The real implementation of each capability, for code the runtime runs
   with the world's: [main], and an external test. Each is a value the code
   owns, with evidence on the stack pointing at it. One that holds something,
   as [SystemConsole] holds the input it has read and not yet given, is made
   by its type's [new]. *)
let real_implementations st ~user capabilities =
  List.map
    (fun capability ->
      let impl = real_implementation capability in
      let ty =
        match Interface.Impls.impl_interface st.context.database impl with
        | Some interface -> Monomorphic.ground st.context.monomorphic [] interface.for_type
        | None ->
            unsupported "%s uses %s, which has no real implementation" user
              (Ground.path_name capability)
      in
      let implementation =
        if is_zero_size st ty then Lir.Constant Null
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

(* The standard library's function that copies bytes into a [String],
   replacing what is not UTF-8. *)
let text_copied_from = Well_known.path Text_copied_from

(* The C [main]'s Truss side: the program's arguments as a [List] of
   [String]s, each made of an argument's bytes by the standard library; the
   real implementation of each capability [main] uses; and [main]'s
   [ExitCode] as the process's status. *)
let program_main context (key : Instance.key) main_path : Lir.t =
  let st = generated_state context ~anchor:main_path ~substitution:[] in
  let b = st.b in
  let count = local b ~name:"count" (Raw (Integer Int32)) in
  let arguments_pointer = local b ~name:"arguments" (Raw (Pointer Opaque)) in
  result_slot st (Returned (Raw (Integer Int32)));
  start b (block b);
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
      (Intrinsics.lower ~checks:context.checks context.env b context.types operation ~type_arguments
         arguments ~destination
         ~site:{ definition = main_path; line = 0; column = 1 })
  in
  let wanted = local b (Value context.types.usize) in
  emit b (Assign (at wanted, Convert (Copy (at count), Integer USize)));
  lower Storage_with_capacity [ string_ty ]
    [ Value (Copy (at wanted)) ]
    (Some (list / Field storage_field));
  loop b ~integer:Int32 ~index_type:(Raw (Integer Int32))
    ~count:(Copy (at count))
    (fun index ->
      let length = local b (Value context.types.usize) and bytes = local b (Raw (Pointer Opaque)) in
      let call intrinsic arguments result =
        emit b (Call { target = Intrinsic intrinsic; arguments; result = Returned (at result) })
      in
      call Program_argument [ Copy (at arguments_pointer); Copy (at index) ] bytes;
      call Terminated_length [ Copy (at bytes) ] length;
      let view_ty = Storage.view_of_elements (Monomorphic.builtin UInt8) in
      let view = temporary st view_ty in
      emit b
        (Assign (view, Storage.view view_ty ~elements:(Copy (at bytes)) ~length:(Copy (at length))));
      let text = temporary st string_ty in
      call_instance st
        (Code { path = text_copied_from; type_arguments = [] })
        ~signature:(signature_of context text_copied_from)
        ~substitution:[]
        ~arguments:[ (Read, view_ty, view) ]
        ~destination:text ();
      lower Storage_push [ string_ty ]
        [ Place (list / Field storage_field); Value (Move text) ]
        None);
  st.evidence <- real_implementations st ~user:"main" (evidence_for st.context [] signature.uses);
  let exit_ty =
    match signature.output with
    | Returns ty -> Monomorphic.ground context.monomorphic [] ty
    | _ -> bug "main yields"
  in
  let exit = temporary st exit_ty in
  call_instance st
    (Code { path = main_path; type_arguments = [] })
    ~signature ~substitution:[]
    ~arguments:[ (list_mode, list_ty, list) ]
    ~destination:exit ();
  (match (Monomorphic.shape context.monomorphic exit_ty, result_place st) with
  | Record [ (field, _) ], Some status ->
      emit b (Assign (status, Convert (Copy (exit / Field field), Integer Int32)))
  | _ -> bug "an ExitCode that is not a record of one field");
  { key; main = finish_function st ~first:[ count; arguments_pointer ] ~rest:[] (); nested = [||] }

(* A named function as a value of a function type. *)
let adapter context (key : Instance.key) ~(function_ : Instance.key) ~(ty : Ground.function_type) :
    Lir.t =
  let path, type_arguments =
    match function_ with
    | Code { path; type_arguments } -> (path, type_arguments)
    | _ -> bug "an adapter"
  in
  let signature = signature_of context path in
  let substitution = bind signature.generics type_arguments in
  let st = generated_state context ~anchor:path ~substitution in
  let b = st.b in
  let environment = local b ~name:"environment" (Raw (Nullable_pointer Opaque)) in
  let result_ty =
    match ty.result with Returns t -> t | _ -> bug "an adapter for a function that yields"
  in
  result_slot st (Convention.result context.env result_ty);
  let parameter_places =
    List.map
      (fun ((mode : Ground.mode), ty) ->
        let types_mode : Types.mode = match mode with Read -> Read | Mut -> Mut | Own -> Own in
        (parameter st ~owned:(mode = Own) mode ty, types_mode, ty))
      ty.parameters
  in
  let evidence = evidence_parameters st ty.uses in
  start b (block b);
  call_instance st function_ ~signature ~substitution
    ~arguments:(List.map (fun ((_, place), mode, ty) -> (mode, ty, place)) parameter_places)
    ~destination:(passed_on st result_ty) ();
  {
    key;
    main =
      finish_function st ~returns:(result_ty <> Never) ~first:[ environment ]
        ~rest:(List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places @ evidence)
        ();
    nested = [||];
  }

(* An entry in an [any] table: the value's pointer as [self], then the
   method's arguments. *)
let any_entry context (key : Instance.key) (method_key : Instance.key) : Lir.t =
  let path, type_arguments =
    match method_key with
    | Code { path; type_arguments } -> (path, type_arguments)
    | _ -> bug "an entry's method"
  in
  let impl, name, receiver =
    match path with
    | Method { owner; name; receiver } -> (owner, name, receiver)
    | _ -> bug "an any entry"
  in
  let interface = impl_interface context impl in
  let trait = interface.implements.trait in
  let _, trait_signature = dynamic_slot context trait name in
  let method_signature = signature_of context path in
  let substitution = bind method_signature.generics type_arguments in
  let any = Types.substitute_trait substitution interface.implements in
  let _, result, capabilities = any_entry_signature context ~any ~trait trait_signature in
  let st = generated_state context ~anchor:impl ~substitution in
  let b = st.b in
  let value = local b ~name:"value" (Raw (Pointer Opaque)) in
  result_slot st result;
  let parameter_places =
    List.map
      (fun (info : Types.parameter_info) ->
        let ty = Monomorphic.ground context.monomorphic substitution info.type_ in
        (parameter st ~owned:(info.mode = Own) (Monomorphic.mode info.mode) ty, info.mode, ty))
      method_signature.parameters
  in
  let evidence = evidence_parameters st capabilities in
  start b (block b);
  let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
  let typed = local b (Pointer { target = Value self_ty; writable = true }) in
  if not (is_zero_size st self_ty) then emit b (Assign (at typed, Use (Copy (at value))));
  let self_mode : Types.mode =
    match receiver with Mut -> Mut | Own -> Own | Read | Static -> Read
  in
  let result_ty =
    match method_signature.output with
    | Returns t -> Monomorphic.ground context.monomorphic substitution t
    | _ -> bug "an any method that yields"
  in
  call_instance st method_key ~signature:method_signature ~substitution
    ~arguments:
      ((self_mode, self_ty, { Lir.root = Local typed; projections = [ Deref ] })
      :: List.map (fun ((_, place), mode, ty) -> (mode, ty, place)) parameter_places)
    ~destination:(passed_on st result_ty) ();
  {
    key;
    main =
      finish_function st
        ~returns:(method_signature.output <> Returns Never)
        ~first:[ value ]
        ~rest:(List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places @ evidence)
        ();
    nested = [||];
  }

(* An [any] table: the type's drop in slot 0, then an entry for each method
   that can be called through [any]. *)
let any_table context (key : Instance.key) : Lir.table =
  match key with
  | Any_table { impl; type_arguments } ->
      let interface = impl_interface context impl in
      let trait = interface.implements.trait in
      let substitution = bind interface.impl_generics type_arguments in
      let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
      let any = Types.substitute_trait substitution interface.implements in
      let drop_signature : Lir.signature =
        { parameters = [ Raw (Pointer Opaque) ]; result = None; returns = true }
      in
      let entries =
        List.map
          (fun (m : Types.trait_method) ->
            let receiver =
              match
                List.find_opt (fun (name, _, _) -> name = m.method_name) interface.impl_methods
              with
              | Some (_, receiver, _) -> receiver
              | None -> m.method_receiver
            in
            let method_key =
              Instance.Code
                { path = Method { owner = impl; name = m.method_name; receiver }; type_arguments }
            in
            ( Instance.Any_entry method_key,
              let signature, _, _ = any_entry_signature context ~any ~trait m.method_signature in
              signature ))
          (any_methods context trait)
      in
      {
        table_key = key;
        capability = None;
        entries = (Instance.Any_drop self_ty, drop_signature) :: entries;
      }
  | _ -> bug "not an any table: %s" (Instance.to_string key)

(* Whether a method of a derived [impl] is the trait's own, written in the
   trait, rather than one the derivation writes. *)
