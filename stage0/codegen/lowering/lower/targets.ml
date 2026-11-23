let resolve_impl (context : Definitions.context) substitution ~(trait : Types.trait_reference)
    ~self_type ~(evidence : Core.evidence) =
  let substitute = Types.substitute substitution in
  let impl, arguments =
    match evidence with
    | Impl { impl; substitution = impl_substitution } ->
        (impl, Types.substitute_substitution substitution impl_substitution)
    | Bound -> (
        let self = context.monomorphic.normalize (substitute self_type) in
        match
          Interface.Impls.find_evidence context.lookups.interface
            ~list_bounds:Interface.Impls.list_no_bounds self
            (let trait = Types.substitute_trait substitution trait in
             {
               trait with
               trait_arguments =
                 List.map
                   (function
                     | Types.Type ty -> Types.Type (context.monomorphic.normalize ty)
                     | argument -> argument)
                   trait.trait_arguments;
             })
        with
        | Some (From_impl { impl; substitution }) -> (impl, substitution)
        | _ ->
            Definitions.raise_bug "no impl of %s for %s" (Types.show_trait trait) (Types.show self))
    | Dynamic -> Definitions.raise_bug "a call through any, which reaches no single impl"
  in
  let impl_interface = Definitions.read_impl_interface context impl in
  let impl_arguments =
    List.map
      (fun (generic : Types.generic) ->
        match Types.find_argument generic.generic arguments with
        | Some argument ->
            Monomorphic.ground_argument context.monomorphic Types.no_substitution argument
        | None -> Definitions.raise_bug "the impl's parameter %s is not bound" generic.generic.name)
      impl_interface.impl_generics
  in
  (impl, impl_arguments)

let make_trait_method_item context substitution ~(trait : Types.trait_reference) ~name ~receiver
    ~self_type ~(instantiation : Types.instantiation) ~(evidence : Core.evidence) =
  let impl, impl_arguments = resolve_impl context substitution ~trait ~self_type ~evidence in
  let own = Monomorphic.ground_instantiation context.monomorphic substitution instantiation in
  Lowered.Item.make_code
    (Method { owner = impl; name; receiver })
    { own with type_arguments = impl_arguments @ own.type_arguments }

let convert_operand state (mode : Language.Mode.t) ty (place : Lowered.place)
    (passed : Lowered.ty option) =
  match passed with
  | None -> None
  | Some (Pointer _) when mode = Language.Mode.Own ->
      ignore (Lowering.move_place state place);
      Some (Lowered.Moved_address place)
  | Some (Pointer { writable; _ }) -> Some (Lowered.Address { place; writable })
  | Some _ -> (
      match mode with
      | Own -> Some (Lowering.make_owned_operand state place ty)
      | Read | Mut -> Some (Copy place))

let pass state (mode : Language.Mode.t) ty place =
  convert_operand state mode ty place (Convention.classify_parameter state.context.env mode ty)

let lookup_method_slot (context : Definitions.context) ~owner ~handle_missing
    (methods : Types.trait_method list) ~is_wanted =
  match List.find_index is_wanted methods with
  | Some index ->
      ( index,
        Interface.Definition.read_method_signature context.lookups.interface ~owner
          (List.nth methods index) )
  | None -> handle_missing ()

let raise_lending_capability_method capability name =
  Lowering.raise_unsupported "`%s.%s`, a capability method that lends" (Path.show capability) name

let lookup_capability_method (context : Definitions.context) capability name =
  let slot, signature =
    lookup_method_slot context ~owner:capability
      (Definitions.read_trait_interface context capability).methods
      ~is_wanted:(fun (declared : Types.trait_method) -> declared.method_name = name)
      ~handle_missing:(fun () ->
        Definitions.raise_bug "%s has no method %s" (Path.show capability) name)
  in
  match signature.output with
  | Returns _ -> (slot, signature)
  | Lends _ -> raise_lending_capability_method capability name

let make_entry_signature context (signature : Types.signature) =
  let entry, result =
    Definitions.make_c_signature context Types.no_substitution
      ~parameters:(Definitions.list_interface_parameters { signature with receiver = None })
      signature.output
  in
  ({ entry with parameters = Convention.evidence :: entry.parameters }, result)

let list_any_slots (context : Definitions.context) ~self (any : Types.trait_reference) =
  let substitution =
    Types.bind_argument
      (Types.make_self_parameter any.trait)
      (Types.Type self) Types.no_substitution
  in
  List.filter_map
    (fun (dispatched : Interface.Impls.dispatched) ->
      match dispatched.through_any with
      | Callable ->
          Some (Types.substitute_trait substitution dispatched.declared_by, dispatched.trait_method)
      | Has_generics | Names_self -> None)
    (Interface.Impls.list_dispatched_methods context.lookups.interface any)

let lookup_dynamic_method context ~(any : Types.trait_reference) trait name receiver =
  let slots = list_any_slots context ~self:(Types.Any any) any in
  match
    List.find_index
      (fun ((bound : Types.trait_reference), (declared : Types.trait_method)) ->
        Path.equal bound.trait trait && declared.method_name = name
        && declared.method_receiver = receiver)
      slots
  with
  | Some index ->
      ( index,
        Interface.Definition.read_method_signature context.lookups.interface ~owner:trait
          (snd (List.nth slots index)) )
  | None -> Definitions.raise_bug "%s cannot be called through any" name

let is_copyable_any (context : Definitions.context) (any : Types.trait_reference) =
  Interface.Impls.is_copyable context.lookups.interface ~list_bounds:Interface.Impls.list_no_bounds
    (Types.Any any)

let make_any_substitution (context : Definitions.context) ~(any : Types.trait_reference) trait :
    Types.substitution =
  let reference =
    match
      List.find_opt
        (fun ((bound : Types.trait_reference), _) -> Path.equal bound.trait trait)
        (list_any_slots context ~self:(Types.Any any) any)
    with
    | Some (bound, _) -> bound
    | None ->
        Definitions.raise_bug "`%s` dispatches no method of %s" (Types.show (Types.Any any))
          (Path.show trait)
  in
  Types.make_trait_substitution (Definitions.read_trait_interface context trait).trait_generics
    ~self:(Types.Any any) reference

let make_any_entry_signature context ~any ~trait (signature : Types.signature) =
  let substitution = make_any_substitution context ~any trait in
  let entry, result =
    Definitions.make_c_signature context substitution
      ~parameters:(Definitions.list_interface_parameters { signature with receiver = None })
      ~uses:signature.uses signature.output
  in
  ( { entry with parameters = Lowered.Raw (Pointer Opaque) :: entry.parameters },
    result,
    Definitions.list_evidence context substitution signature.uses )

let extend_evidence (state : Lowering.state) ~(site : Lowered.site option) capability evidence =
  match site with
  | Some site when Path.equal capability Definitions.panic_path ->
      let link = Emit_c.Ir_builder.allocate_local state.builder Trace in
      Emit_c.Ir_builder.emit state.builder
        (Call
           {
             target = Intrinsic Trace_link;
             arguments =
               [
                 Address { place = Lowered.make_local_place link; writable = true };
                 Constant (Site site);
                 evidence;
               ];
             result = Discarded;
           });
      Lowered.Address { place = Lowered.make_local_place link; writable = false }
  | Some _ | None -> evidence

let lower_implementation_evidence (state : Lowering.state) ~impl ~type_arguments ~implementation
    ~site =
  let outer =
    List.map
      (fun captured ->
        match List.find_opt (fun (path, _) -> Path.equal path captured) state.evidence with
        | Some (_, operand) -> extend_evidence state ~site captured operand
        | None -> Definitions.raise_bug "no evidence for %s here" (Path.show captured))
      (Definitions.list_evidence state.context Types.no_substitution
         (Definitions.read_impl_interface state.context impl).impl_uses)
  in
  let slot = Emit_c.Ir_builder.allocate_local state.builder (Evidence (List.length outer)) in
  Emit_c.Ir_builder.emit state.builder
    (Call
       {
         target = Intrinsic Evidence_fill;
         arguments =
           Address { place = Lowered.make_local_place slot; writable = true }
           :: implementation
           :: Constant (Symbol_address (Table (Impl_table { impl; type_arguments })))
           :: outer;
         result = Discarded;
       });
  Lowered.Address { place = Lowered.make_local_place slot; writable = false }

let lookup_evidence (state : Lowering.state) capability =
  match List.find_opt (fun (path, _) -> Path.equal path capability) state.evidence with
  | Some (_, operand) -> operand
  | None -> (
      let raise_missing () =
        Definitions.raise_bug "no evidence for %s here" (Path.show capability)
      in
      match state.frame.code.enclosing_impl with
      | Some impl
        when Path.equal (Definitions.read_impl_interface state.context impl).implements.trait
               capability ->
          let interface = Definitions.read_impl_interface state.context impl in
          let self_ty =
            Monomorphic.ground state.context.monomorphic state.frame.code.substitution
              interface.for_type
          in
          let implementation =
            match state.frame.self_place with
            | _ when Memory_layout.has_zero_size state.context.env self_ty -> Lowered.Constant Null
            | Some self -> Lowered.Address { place = self; writable = true }
            | None -> raise_missing ()
          in
          let type_arguments =
            List.map
              (fun (generic : Types.generic) ->
                match Types.find_argument generic.generic state.frame.code.substitution with
                | Some argument ->
                    Monomorphic.ground_argument state.context.monomorphic Types.no_substitution
                      argument
                | None -> Definitions.raise_bug "an unbound parameter of %s" (Path.show impl))
              interface.impl_generics
          in
          lower_implementation_evidence state ~impl ~type_arguments ~implementation ~site:None
      | _ -> raise_missing ())

let pass_evidence (state : Lowering.state) ~site capability =
  extend_evidence state ~site capability (lookup_evidence state capability)

let pass_capabilities (state : Lowering.state) ~site capabilities =
  match capabilities with
  | [] -> Lowered.Constant Null
  | _ ->
      let table =
        Emit_c.Ir_builder.allocate_local state.builder (Capabilities (List.length capabilities))
      in
      Emit_c.Ir_builder.emit state.builder
        (Call
           {
             target = Intrinsic Capabilities_fill;
             arguments =
               Address { place = Lowered.make_local_place table; writable = true }
               :: List.concat_map
                    (fun capability ->
                      [
                        Lowered.Constant (Capability capability);
                        pass_evidence state ~site capability;
                      ])
                    capabilities;
             result = Discarded;
           });
      Lowered.Address { place = Lowered.make_local_place table; writable = false }

let lower_nested_function (state : Lowering.state) ~(function_type : Ground.function_type)
    ~(output : Types.result option) ~(captures : (Lowered.place * Ground.ty) list)
    ~(body :
       Lowering.state ->
       captures:Lowered.place list ->
       (Lowered.place * Language.Mode.t * Ground.ty) list ->
       unit) destination =
  let index = !(state.nested) in
  incr state.nested;
  let captured =
    List.mapi
      (fun position (place, ty) -> (Printf.sprintf "capture%d" position, place, ty))
      captures
  in
  let environment =
    List.map
      (fun (name, _, ty) -> (name, Lowered.Pointer { target = Value ty; writable = false }))
      captured
  in
  Emit_c.Ir_builder.build_nested state.builder ~index ~environment (fun builder ->
      let environment_local =
        Lowered.make_local_place
          (Emit_c.Ir_builder.allocate_local state.builder (Environment index))
      in
      List.iter
        (fun (name, place, _) ->
          Emit_c.Ir_builder.emit state.builder
            (Assign
               ( Lowered.project environment_local (Field name),
                 Use (Address { place; writable = false }) )))
        captured;
      Emit_c.Ir_builder.emit state.builder
        (Assign
           ( destination,
             Function_value
               {
                 code = Nested index;
                 environment = Some (Address { place = environment_local; writable = false });
               } ));
      let inner =
        Lowering.enter state.context ~nested:state.nested ~builder
          {
            state.frame with
            exit = None;
            code =
              (match output with
              | Some output -> { state.frame.code with result = output }
              | None -> state.frame.code);
          }
      in
      let environment_parameter =
        Emit_c.Ir_builder.allocate_local builder (Raw (Nullable_pointer Opaque))
      in
      Lowering.set_result_slot inner
        (Convention.classify_result state.context.env function_type.result);
      let parameter_places =
        List.map
          (fun ((mode : Language.Mode.t), ty) ->
            (Lowering.allocate_parameter inner ~in_scope:false ~owned:(mode = Own) mode ty, mode, ty))
          function_type.parameters
      in
      let capabilities = Emit_c.Ir_builder.allocate_local builder Convention.capabilities in
      let environment_pointer =
        Emit_c.Ir_builder.allocate_local builder
          (Pointer { target = Environment index; writable = false })
      in
      Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder);
      Emit_c.Ir_builder.emit builder
        (Assign
           ( Lowered.make_local_place environment_pointer,
             Use (Copy (Lowered.make_local_place environment_parameter)) ));
      Lowering.look_up_capabilities inner
        ~table:(Copy (Lowered.make_local_place capabilities))
        function_type.uses;
      body inner
        ~captures:
          (List.map
             (fun (name, _, _) ->
               {
                 Lowered.root = Local environment_pointer;
                 projections = [ Deref; Field name; Deref ];
               })
             captured)
        (List.map (fun ((_, place), mode, ty) -> (place, mode, ty)) parameter_places);
      Lowering.finish_function inner ~first:[ environment_parameter ]
        ~rest:
          (List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places @ [ capabilities ])
        ())

let is_unreachable_panic (state : Lowering.state) capabilities =
  state.frame.code.assumes_condition
  && Option.is_none (Lowering.find_panic_trace state)
  && List.exists (Path.equal Definitions.panic_path) capabilities

let lower_indirect_call state ~(function_type : Ground.function_type) ~(value : Lowered.place) ~site
    (places : Lowered.place list) destination =
  if is_unreachable_panic state function_type.uses then Lowering.emit_unreachable_block state
  else
    let passed =
      List.concat
        (List.map2
           (fun ((mode : Language.Mode.t), ty) place -> Option.to_list (pass state mode ty place))
           function_type.parameters places)
      @ [ pass_capabilities state ~site function_type.uses ]
    in
    let target =
      Lowered.Indirect
        {
          code = Copy (Builtin_records.Function_value.project_code value);
          environment = Copy (Builtin_records.Function_value.project_environment value);
          signature = Convention.make_function_value_signature state.context.env function_type;
        }
    in
    Emit_c.Ir_builder.emit state.builder
      (Call
         {
           target;
           arguments = passed;
           result =
             Convention.make_destination
               (Convention.classify_result state.context.env function_type.result)
               destination;
         });
    if function_type.result = Never then Lowering.emit_unreachable_block state

let lower_call_through_any (state : Lowering.state) ~(any_type : Types.trait_reference) ~trait ~name
    ~receiver ~(any : Lowered.place)
    ~(arguments : (Language.Mode.t * Ground.ty * Lowered.place) list) ?(lending = []) ~site
    destination =
  let index, signature = lookup_dynamic_method state.context ~any:any_type trait name receiver in
  let slot =
    Drop_and_copy.compute_first_method_slot ~is_copyable:(is_copyable_any state.context any_type)
    + index
  in
  let c_signature, result, capabilities =
    make_any_entry_signature state.context ~any:any_type ~trait signature
  in
  if is_unreachable_panic state capabilities then Lowering.emit_unreachable_block state
  else
    let passed = List.filter_map (fun (mode, ty, place) -> pass state mode ty place) arguments in
    let evidence = List.map (pass_evidence state ~site) capabilities in
    if receiver = Path.Instance Own then ignore (Lowering.move_place state any);
    let target =
      Lowered.Table_call
        {
          table = Copy (Builtin_records.Any.project_vtable any);
          value = Copy (Builtin_records.Any.project_value any);
          slot;
          signature = c_signature;
        }
    in
    Emit_c.Ir_builder.emit state.builder
      (Call
         {
           target;
           arguments = passed @ evidence @ lending;
           result = Convention.make_destination result destination;
         });
    if not c_signature.returns then Lowering.emit_unreachable_block state

let run_in_type_definition (state : Lowering.state) ~(source : Resolve.Names.key) (ty : Ground.ty)
    nested_function =
  let path, arguments =
    match ty with
    | Named { path; arguments } -> (path, arguments)
    | _ -> Definitions.raise_bug "defaults of %s" (Ground.to_string ty)
  in
  let interface = Interface.Definition.read_type_interface state.context.lookups.interface path in
  let caller = state.frame in
  state.frame <-
    {
      caller with
      code =
        {
          caller.code with
          definition = source.path;
          written = Some (Definitions.read_written state.context source);
          enclosing_impl = None;
          substitution = Definitions.bind interface.type_generics arguments;
        };
      self_place = None;
    };
  let result = nested_function () in
  state.frame <- caller;
  result

let begin_output state =
  let output = Lowering.allocate_temporary state Writing.output_ty in
  Emit_c.Ir_builder.emit state.builder (Assign (output, Storage.build_empty Writing.output_ty));
  output

let echo state place ty ~site =
  let output = begin_output state in
  Debug_output.emit_debug_call state.context.env state.builder
    ~output:(Address { place = output; writable = true })
    ty place;
  Emit_c.Ir_builder.emit state.builder
    (Echo
       {
         text = Copy (Storage.project_buffer output);
         length = Copy (Storage.project_length output);
         site;
       })

let lower_any_into (state : Lowering.state) ~any_ty ~inner_ty ~impl ~type_arguments
    ~(value : Lowered.place) destination =
  let box = Drop_and_copy.allocate_box state.context.drop_and_copy state.builder inner_ty in
  if not (Lowering.is_zero_size state inner_ty) then begin
    let typed =
      Emit_c.Ir_builder.allocate_local state.builder
        (Pointer { target = Value inner_ty; writable = true })
    in
    Emit_c.Ir_builder.emit state.builder
      (Assign (Lowered.make_local_place typed, Use (Copy (Lowered.make_local_place box))));
    Emit_c.Ir_builder.emit state.builder
      (Assign
         (Lowered.make_deref_place typed, Use (Lowering.make_owned_operand state value inner_ty)))
  end;
  Emit_c.Ir_builder.emit state.builder
    (Assign
       ( destination,
         Builtin_records.Any.build any_ty
           ~value:(Copy (Lowered.make_local_place box))
           ~vtable:(Constant (Symbol_address (Table (Any_table { impl; type_arguments })))) ))

let lower_provided_evidence (state : Lowering.state) ~(implementation : Lowered.operand) ~site
    provides =
  List.map
    (fun (capability, impl, (arguments : Types.substitution)) ->
      let type_arguments =
        List.map
          (fun (generic : Types.generic) ->
            match Types.find_argument generic.generic arguments with
            | Some argument ->
                Monomorphic.ground_argument state.context.monomorphic state.frame.code.substitution
                  argument
            | None -> Definitions.raise_bug "an unbound parameter of %s" (Path.show impl))
          (Definitions.read_impl_interface state.context impl).impl_generics
      in
      (capability, lower_implementation_evidence state ~impl ~type_arguments ~implementation ~site))
    provides

let lower_item_call (state : Lowering.state) item ~(signature : Types.signature) ~substitution
    ~(arguments : (Language.Mode.t * Ground.ty * Lowered.place) list) ?(lending = []) ~destination
    ~site () =
  let item : Lowered.Item.t =
    match item with
    | Lowered.Item.Code { path; instantiation; assumes_condition = false }
      when Definitions.has_panic_condition signature.uses
           && Option.is_none (Lowering.find_panic_trace state) ->
        Lowered.Item.Code { path; instantiation; assumes_condition = true }
    | item -> item
  in
  let uses =
    match item with
    | Lowered.Item.Code { assumes_condition = true; _ } ->
        Definitions.remove_panic_condition signature.uses
    | _ -> signature.uses
  in
  if is_unreachable_panic state (Definitions.list_evidence state.context substitution uses) then
    Lowering.emit_unreachable_block state
  else
    let c_signature, result =
      Definitions.make_c_signature state.context substitution
        ~parameters:(Definitions.list_interface_parameters signature)
        ~uses signature.output
    in
    let passed = List.filter_map (fun (mode, ty, place) -> pass state mode ty place) arguments in
    let evidence =
      List.map (pass_evidence state ~site)
        (Definitions.list_evidence state.context substitution uses)
    in
    let target = Lowered.Direct { function_ = Item item; signature = c_signature } in
    Emit_c.Ir_builder.emit state.builder
      (Call
         {
           target;
           arguments = passed @ evidence @ lending;
           result = Convention.make_destination result destination;
         });
    if not c_signature.returns then Lowering.emit_unreachable_block state

type literal = Integer_value of Z.t | Float_value of float

let lower_literal state ty (literal : literal) : Lowered.operand =
  match (literal, Lowering.classify_scalar state ty) with
  | Integer_value value, Integer integer -> Lowering.make_int_constant integer value
  | Integer_value value, Character -> Constant (Character (Z.to_int value))
  | Float_value value, Float64 -> Constant (Float64 (Int64.bits_of_float value))
  | Float_value value, Float32 -> Constant (Float32 (Int32.bits_of_float value))
  | _ -> Definitions.raise_bug "a literal of type %s" (Ground.to_string ty)

let rec make_static_literal monomorphic (ty : Ground.ty) (literal : Language.Literal.t) :
    Lowered.static_value =
  let make_elements element : Lowered.static_value list =
    match literal with
    | Text text ->
        List.init (String.length text) (fun index ->
            Lowered.Static_scalar (Integer (UInt8, Z.of_int (Char.code text.[index]))))
    | Elements elements -> List.map (make_static_literal monomorphic element) elements
  in
  match (Storage.find_storage_element ty, Storage.find_view_element ty) with
  | Some element, _ ->
      let elements = make_elements element in
      Static_storage { element; elements; capacity = List.length elements }
  | None, Some element -> Static_view { element; elements = make_elements element }
  | None, None -> (
      match Monomorphic.compute_shape monomorphic ty with
      | Record [ (field, Typed part) ] ->
          Static_record [ (field, make_static_literal monomorphic part literal) ]
      | _ -> Definitions.raise_bug "a literal of type %s" (Ground.to_string ty))

let lower_literal_place (state : Lowering.state) (ty : Ground.ty) literal =
  let built = Lowering.allocate_local state (Value ty) in
  Emit_c.Ir_builder.emit state.builder
    (Assign (built, Data { ty; value = make_static_literal state.context.monomorphic ty literal }));
  built

let lower_owner_of_view (state : Lowering.state) ~(owner : Ground.ty) ~(view : Ground.ty)
    (viewed : Lowered.place) (destination : Lowered.place) =
  let storage_field, storage =
    match Monomorphic.compute_shape state.context.monomorphic owner with
    | Record [ (field, Typed storage) ] when Storage.find_storage_element storage <> None ->
        (field, storage)
    | _ -> Definitions.raise_bug "%s owns no storage" (Ground.to_string owner)
  in
  let view_place =
    match Monomorphic.compute_shape state.context.monomorphic view with
    | Record [ (field, Typed field_ty) ] when Storage.find_view_element field_ty <> None ->
        Lowered.project viewed (Field field)
    | _ -> Definitions.raise_bug "%s views no storage" (Ground.to_string view)
  in
  let built = Lowering.allocate_local state (Value storage) in
  Emit_c.Ir_builder.emit state.builder
    (Assign
       ( built,
         Storage.build_borrowed storage
           ~buffer:(Copy (Storage.project_buffer view_place))
           ~length:(Copy (Storage.project_length view_place)) ));
  Emit_c.Ir_builder.emit state.builder
    (Assign
       (destination, Build { ty = owner; variant = None; fields = [ (storage_field, Copy built) ] }))

let lower_static_constant (state : Lowering.state) path : Lowered.place =
  let ty = Interface.Definition.read_constant_type state.context.lookups.interface path in
  { root = Static { item = Constant path; ty = Lowering.ground state ty }; projections = [] }

let read_list_parts monomorphic ty =
  match Monomorphic.compute_shape monomorphic ty with
  | Record [ (field, Typed storage) ] -> (
      match Storage.find_storage_element storage with
      | Some element -> (field, storage, element)
      | None -> Definitions.raise_bug "%s is not a list" (Ground.to_string ty))
  | _ -> Definitions.raise_bug "%s is not a list" (Ground.to_string ty)

let pull_loop state ~(option : Ground.ty) ~(call_next : Lowered.place -> unit)
    ~(body : Lowered.place -> unit) =
  Lowering.run_in_scope state (fun () ->
      let next = Lowering.allocate_local state (Value option) in
      let depth = List.length state.scopes in
      let test = Emit_c.Ir_builder.allocate_block state.builder
      and inside = Emit_c.Ir_builder.allocate_block state.builder
      and after = Emit_c.Ir_builder.allocate_block state.builder in
      Emit_c.Ir_builder.finish state.builder (Goto test);
      Emit_c.Ir_builder.start state.builder test;
      call_next next;
      let some_variant = Well_known.show_variant Option_some in
      Emit_c.Ir_builder.finish state.builder
        (Switch_variant { place = next; cases = [ (some_variant, inside) ]; default = Some after });
      Emit_c.Ir_builder.start state.builder inside;
      Lowering.run_in_scope state (fun () ->
          Lowering.run_in_loop state ~continue_:test ~break_:after ~depth (fun () ->
              body
                (Lowered.project next
                   (Variant_field
                      { variant = some_variant; field = Well_known.show_field Option_some_value }))));
      Emit_c.Ir_builder.finish state.builder (Goto test);
      Emit_c.Ir_builder.start state.builder after)
