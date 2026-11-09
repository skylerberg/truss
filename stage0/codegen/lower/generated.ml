(* Instances lowering makes rather than finds in source: capability
   entries and tables, the real implementations' evidence, the program's
   main, adapters, and [any] entries and tables. See lower.ml. *)

open Definitions
open Lowering
open Targets
open Lir_builder

let generated_state context ~anchor ~substitution =
  let code =
    {
      definition_key =
        { Names.module_ = { package = ""; modules = [] }; path = anchor; ordinal = 0 };
      anchor;
      text = "";
      checked = Checked.create 0;
      parameters = [];
      body = { statements = []; span = S.Span.make 0 0; id = 0 };
      result = Returns T.unit;
      parameter_types = [];
      substitution;
      uses = [];
      has_defaults = false;
      requires = [];
    }
  in
  {
    context;
    frame =
      {
        code;
        bindings = Hashtbl.create 1;
        self_place = None;
        on_yield = None;
        inlined = [];
        exit = None;
      };
    b = Lir_builder.create ();
    scopes = [ { owned = [] } ];
    loops = [];
    temporaries = [];
    return_ = None;
    result_local = None;
    nested = ref [];
    evidence = [];
    pulling = false;
  }

(* The capability an [impl] implements, and the capabilities its own
   methods use, in path order, which its evidence captures. *)
let impl_capability context impl =
  let interface = impl_interface context impl in
  (interface, interface.implements.trait, evidence_for [] interface.impl_uses)

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
  let entry_lir, result = entry_signature context capability_signature in
  let method_signature = signature_of context path in
  let substitution = bind method_signature.generics type_arguments in
  let st = generated_state context ~anchor:impl ~substitution in
  let b = st.b in
  let evidence = local b ~name:"evidence" Convention.evidence in
  let result_pointer =
    match result with Through_pointer pointer -> Some (local b ~name:"result" pointer) | _ -> None
  in
  let parameters =
    List.map
      (fun (info : T.parameter_info) ->
        let ty = Monomorphic.ground context.monomorphic substitution info.type_ in
        match Convention.parameter context.env (Monomorphic.mode info.mode) ty with
        | Some (Pointer _ as pointer) ->
            let l = local b pointer in
            (Some l, ({ Lir.root = Local l; projections = [ Deref ] } : Lir.place), info.mode, ty)
        | Some lir_ty ->
            let l = local b lir_ty in
            (Some l, at l, info.mode, ty)
        | None -> (None, new_local st ty, info.mode, ty))
      capability_signature.parameters
  in
  start b (block b);
  let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
  let implementation = local b (Pointer { target = Value self_ty; writable = true }) in
  if not (zero_size st self_ty) then
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
  let self_mode : T.mode = match receiver with Mut -> Mut | Own -> Own | Read | Static -> Read in
  let result_ty =
    match capability_signature.output with
    | Returns ty -> Monomorphic.ground context.monomorphic [] ty
    | _ -> bug "a capability method that yields"
  in
  let destination =
    match result_pointer with
    | Some pointer -> { Lir.root = Local pointer; projections = [ Deref ] }
    | None -> new_local st result_ty
  in
  call_instance st method_key ~signature:method_signature ~substitution
    ~arguments:
      ((self_mode, self_ty, { Lir.root = Local implementation; projections = [ Deref ] })
      :: List.map (fun (_, place, mode, ty) -> (mode, ty, place)) parameters)
    ~mask:0 ~destination;
  finish b (Return (match result with Returned _ -> Some (Lir.Move destination) | _ -> None));
  let main =
    Lir_builder.build b ?written_result:result_pointer
      ~parameters:
        ((evidence :: Option.to_list result_pointer)
        @ List.filter_map (fun (l, _, _, _) -> l) parameters)
      ~result:(match result with Returned ty -> Some ty | _ -> None)
  in
  ignore entry_lir;
  {
    key;
    main = { main with returns = capability_signature.output <> Returns Never };
    nested = [||];
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
          (fun (m : T.trait_method) ->
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
      { table_key = key; entries }
  | _ -> bug "not a table: %s" (Instance.to_string key)

(* The [impl] of a standard capability by its real implementation: the
   standard library's [System] type for it, such as [SystemConsole]. *)
let real_implementation (capability : Path.t) : Path.t =
  let name = Ground.path_name capability in
  Impl
    {
      module_ = { package = "standard"; modules = [ "capabilities" ] };
      name = Printf.sprintf "%s for System%s" name name;
    }

let real_evidence _context (capability : Path.t) : Lir.evidence =
  {
    evidence_key = Real_evidence capability;
    table = Table { impl = real_implementation capability; type_arguments = [] };
    outer = [];
  }

(* The C [main]'s Truss side: the program's arguments as a [List] of
   [String]s, whose bytes are the arguments' own, so they are never copied
   unless bad UTF-8 in them has to be replaced; evidence for the real
   implementation of each capability [main] uses; and [main]'s [ExitCode]
   as the process's status. *)
let program_main context (key : Instance.key) main_path : Lir.t =
  let st = generated_state context ~anchor:main_path ~substitution:[] in
  let b = st.b in
  let count = local b ~name:"count" (Raw (Integer Int32)) in
  let arguments_pointer = local b ~name:"arguments" (Raw (Pointer Opaque)) in
  start b (block b);
  let signature = signature_of context main_path in
  let list_ty, list_mode =
    match signature.parameters with
    | [ info ] -> (Monomorphic.ground context.monomorphic [] info.type_, info.mode)
    | _ -> bug "main takes its arguments"
  in
  let string_ty, storage_field, storage_ty =
    match Monomorphic.shape context.monomorphic list_ty with
    | Record [ (field, Typed storage) ] -> (
        match Monomorphic.kind context.monomorphic storage with
        | Storage element -> (element, field, storage)
        | _ -> bug "a List that is not storage")
    | _ -> bug "main's arguments are not a List"
  in
  ignore storage_ty;
  let list = new_local st list_ty in
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
  let index = local b (Raw (Integer Int32)) in
  emit b (Assign (at index, Use (Constant (Integer (Int32, Z.zero)))));
  let test = block b and inside = block b and after = block b in
  finish b (Goto test);
  start b test;
  let going = local b (Raw Bool) in
  emit b (Assign (at going, Binary (Less, Copy (at index), Copy (at count))));
  finish b (Switch { value = Copy (at going); cases = [ (Z.one, inside) ]; default = Some after });
  start b inside;
  let length = local b (Value context.types.usize) and bytes = local b (Raw (Pointer Opaque)) in
  emit b
    (Call
       {
         target = Intrinsic Program_argument;
         arguments =
           [
             Copy (at arguments_pointer);
             Copy (at index);
             Address { place = at length; writable = true };
           ];
         result = Returned (at bytes);
       });
  let text = new_local st string_ty in
  (match Monomorphic.shape context.monomorphic string_ty with
  | Record [ (field, Typed storage) ] ->
      emit b
        (Assign
           ( text / Field field,
             Build
               {
                 ty = storage;
                 variant = None;
                 fields =
                   [
                     ("buffer", Copy (at bytes)); ("length", Copy (at length)); ("capacity", usize 0);
                   ];
               } ))
  | _ -> bug "a String that is not storage");
  lower Storage_push [ string_ty ] [ Place (list / Field storage_field); Value (Move text) ] None;
  emit b (Assign (at index, Binary (Add, Copy (at index), Constant (Integer (Int32, Z.one)))));
  finish b (Goto test);
  start b after;
  st.evidence <-
    List.map
      (fun capability ->
        if Interface.Impls.impl_interface context.database (real_implementation capability) = None
        then
          invalid_arg
            (Printf.sprintf "main uses %s, which stage0's runtime has no real implementation of yet"
               (Ground.path_name capability));
        (capability, Lir.Constant (Symbol_address (Real_evidence capability))))
      (evidence_for [] signature.uses);
  let exit_ty =
    match signature.output with
    | Returns ty -> Monomorphic.ground context.monomorphic [] ty
    | _ -> bug "main yields"
  in
  let exit = new_local st exit_ty in
  call_instance st
    (Code { path = main_path; type_arguments = [] })
    ~signature ~substitution:[]
    ~arguments:[ (list_mode, list_ty, list) ]
    ~mask:0 ~destination:exit;
  emit b (Drop list);
  let status = local b (Raw (Integer Int32)) in
  (match Monomorphic.shape context.monomorphic exit_ty with
  | Record [ (field, _) ] ->
      emit b (Assign (at status, Convert (Copy (exit / Field field), Integer Int32)))
  | _ -> bug "an ExitCode that is not a record of one field");
  finish b (Return (Some (Copy (at status))));
  {
    key;
    main =
      Lir_builder.build b ~parameters:[ count; arguments_pointer ]
        ~result:(Some (Raw (Integer Int32)));
    nested = [||];
  }

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
  let result = Convention.result context.env result_ty in
  let result_pointer =
    match result with Through_pointer pointer -> Some (local b ~name:"result" pointer) | _ -> None
  in
  let parameters =
    List.map
      (fun ((mode : Ground.mode), ty) ->
        let types_mode : T.mode = match mode with Read -> Read | Mut -> Mut | Own -> Own in
        match Convention.parameter context.env mode ty with
        | Some (Pointer _ as pointer) ->
            let l = local b pointer in
            (Some l, (types_mode, ty, ({ Lir.root = Local l; projections = [ Deref ] } : Lir.place)))
        | Some lir_ty ->
            let l = local b lir_ty in
            (Some l, (types_mode, ty, at l))
        | None -> (None, (types_mode, ty, new_local st ty)))
      ty.parameters
  in
  let evidence =
    List.map (fun capability -> (capability, local b ~name:"evidence" Convention.evidence)) ty.uses
  in
  start b (block b);
  st.evidence <- List.map (fun (capability, l) -> (capability, Lir.Copy (at l))) evidence;
  let destination =
    match result_pointer with
    | Some p -> { Lir.root = Local p; projections = [ Deref ] }
    | None -> new_local st result_ty
  in
  call_instance st function_ ~signature ~substitution ~arguments:(List.map snd parameters) ~mask:0
    ~destination;
  finish b (Return (match result with Returned _ -> Some (Lir.Move destination) | _ -> None));
  let main =
    Lir_builder.build b ?written_result:result_pointer
      ~parameters:
        ((environment :: Option.to_list result_pointer)
        @ List.filter_map fst parameters @ List.map snd evidence)
      ~result:(match result with Returned t -> Some t | _ -> None)
  in
  { key; main = { main with returns = result_ty <> Never }; nested = [||] }

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
  let _, result = any_entry_signature context trait_signature in
  let st = generated_state context ~anchor:impl ~substitution in
  let b = st.b in
  let value = local b ~name:"value" (Raw (Pointer Opaque)) in
  let result_pointer =
    match result with Through_pointer pointer -> Some (local b ~name:"result" pointer) | _ -> None
  in
  let parameters =
    List.map
      (fun (info : T.parameter_info) ->
        let ty = Monomorphic.ground context.monomorphic substitution info.type_ in
        match Convention.parameter context.env (Monomorphic.mode info.mode) ty with
        | Some (Pointer _ as pointer) ->
            let l = local b pointer in
            (Some l, (info.mode, ty, ({ Lir.root = Local l; projections = [ Deref ] } : Lir.place)))
        | Some lir_ty ->
            let l = local b lir_ty in
            (Some l, (info.mode, ty, at l))
        | None -> (None, (info.mode, ty, new_local st ty)))
      method_signature.parameters
  in
  let evidence =
    List.map
      (fun capability -> (capability, local b ~name:"evidence" Convention.evidence))
      (evidence_for [] trait_signature.uses)
  in
  start b (block b);
  st.evidence <- List.map (fun (capability, l) -> (capability, Lir.Copy (at l))) evidence;
  let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
  let typed = local b (Pointer { target = Value self_ty; writable = true }) in
  if not (zero_size st self_ty) then emit b (Assign (at typed, Use (Copy (at value))));
  let self_mode : T.mode = match receiver with Mut -> Mut | Own -> Own | Read | Static -> Read in
  let result_ty =
    match method_signature.output with
    | Returns t -> Monomorphic.ground context.monomorphic substitution t
    | _ -> bug "an any method that yields"
  in
  let destination =
    match result_pointer with
    | Some p -> { Lir.root = Local p; projections = [ Deref ] }
    | None -> new_local st result_ty
  in
  call_instance st method_key ~signature:method_signature ~substitution
    ~arguments:
      ((self_mode, self_ty, { Lir.root = Local typed; projections = [ Deref ] })
      :: List.map snd parameters)
    ~mask:0 ~destination;
  finish b (Return (match result with Returned _ -> Some (Lir.Move destination) | _ -> None));
  let main =
    Lir_builder.build b ?written_result:result_pointer
      ~parameters:
        ((value :: Option.to_list result_pointer)
        @ List.filter_map fst parameters @ List.map snd evidence)
      ~result:(match result with Returned t -> Some t | _ -> None)
  in
  { key; main = { main with returns = method_signature.output <> Returns Never }; nested = [||] }

(* An [any] table: the type's drop in slot 0, then an entry for each method
   that can be called through [any]. *)
let any_table context (key : Instance.key) : Lir.table =
  match key with
  | Any_table { impl; type_arguments } ->
      let interface = impl_interface context impl in
      let trait = interface.implements.trait in
      let substitution = bind interface.impl_generics type_arguments in
      let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
      let drop_signature : Lir.signature =
        { parameters = [ Raw (Pointer Opaque) ]; result = None; returns = true }
      in
      let entries =
        List.map
          (fun (m : T.trait_method) ->
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
            (Instance.Any_entry method_key, fst (any_entry_signature context m.method_signature)))
          (any_methods context trait)
      in
      { table_key = key; entries = (Instance.Any_drop self_ty, drop_signature) :: entries }
  | _ -> bug "not an any table: %s" (Instance.to_string key)

(* Whether a method of a derived [impl] is the trait's own, written in the
   trait, rather than one the derivation writes. *)
