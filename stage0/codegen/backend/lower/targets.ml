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
  Lowered.Item.Code
    {
      path = Method { owner = impl; name; receiver };
      instantiation = { own with type_arguments = impl_arguments @ own.type_arguments };
    }

let convert_operand st (mode : Types.mode) ty (place : Lowered.place) (passed : Lowered.ty option) =
  match passed with
  | None -> None
  | Some (Pointer _) when mode = Types.Own ->
      ignore (Lowering.move_place st place);
      Some (Lowered.Moved_address place)
  | Some (Pointer { writable; _ }) -> Some (Lowered.Address { place; writable })
  | Some _ -> (
      match mode with
      | Own -> Some (Lowering.make_owned_operand st place ty)
      | Read | Mut -> Some (Copy place))

let pass st (mode : Types.mode) ty place =
  convert_operand st mode ty place
    (Convention.classify_parameter st.context.env (Monomorphic.ground_mode mode) ty)

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
      ~has_defaults:false signature.output
  in
  ({ entry with parameters = Convention.evidence :: entry.parameters }, result)

let is_callable_through_any (context : Definitions.context) trait
    (trait_method : Types.trait_method) =
  trait_method.method_receiver <> Static
  && Interface.Impls.classify_through_any context.lookups.interface ~trait trait_method = Callable

let list_any_methods (context : Definitions.context) trait =
  List.filter
    (is_callable_through_any context trait)
    (Definitions.read_trait_interface context trait).methods

let lookup_dynamic_method context trait name receiver =
  lookup_method_slot context ~owner:trait (list_any_methods context trait)
    ~is_wanted:(fun (declared : Types.trait_method) ->
      declared.method_name = name && declared.method_receiver = receiver)
    ~handle_missing:(fun () -> Definitions.raise_bug "%s cannot be called through any" name)

let is_copyable_any (context : Definitions.context) (any : Types.trait_reference) =
  Interface.Impls.is_copyable context.lookups.interface ~list_bounds:Interface.Impls.list_no_bounds
    (Types.Any any)

let make_any_substitution (context : Definitions.context) ~(any : Types.trait_reference) trait :
    Types.substitution =
  let reference =
    if Path.equal trait any.trait then any
    else
      match
        List.find_opt
          (fun (bound : Types.trait_reference) -> Path.equal bound.trait trait)
          (Interface.Properties.list_bound_closure context.lookups.interface ~self:(Types.Any any)
             any)
      with
      | Some bound -> bound
      | None ->
          Definitions.raise_bug "%s is not a trait of %s" (Path.show trait)
            (Types.show (Types.Any any))
  in
  Types.make_trait_substitution (Definitions.read_trait_interface context trait).trait_generics
    ~self:(Types.Any any) reference

let make_any_entry_signature context ~any ~trait (signature : Types.signature) =
  let substitution = make_any_substitution context ~any trait in
  let entry, result =
    Definitions.make_c_signature context substitution
      ~parameters:(Definitions.list_interface_parameters { signature with receiver = None })
      ~has_defaults:false ~uses:signature.uses signature.output
  in
  ( { entry with parameters = Lowered.Raw (Pointer Opaque) :: entry.parameters },
    result,
    Definitions.list_evidence context substitution signature.uses )

let extend_evidence (st : Lowering.state) ~(site : Lowered.site option) capability evidence =
  match site with
  | Some site when Path.equal capability Definitions.panic_path ->
      let link = Emit_c.Ir_builder.allocate_local st.builder Trace in
      Emit_c.Ir_builder.emit st.builder
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

let lower_implementation_evidence (st : Lowering.state) ~impl ~type_arguments ~implementation ~site
    =
  let outer =
    List.map
      (fun captured ->
        match List.find_opt (fun (path, _) -> Path.equal path captured) st.evidence with
        | Some (_, operand) -> extend_evidence st ~site captured operand
        | None -> Definitions.raise_bug "no evidence for %s here" (Path.show captured))
      (Definitions.list_evidence st.context Types.no_substitution
         (Definitions.read_impl_interface st.context impl).impl_uses)
  in
  let slot = Emit_c.Ir_builder.allocate_local st.builder (Evidence (List.length outer)) in
  Emit_c.Ir_builder.emit st.builder
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

let lookup_evidence (st : Lowering.state) capability =
  match List.find_opt (fun (path, _) -> Path.equal path capability) st.evidence with
  | Some (_, operand) -> operand
  | None -> (
      let raise_missing () =
        Definitions.raise_bug "no evidence for %s here" (Path.show capability)
      in
      match st.frame.code.enclosing_impl with
      | Some impl
        when Path.equal (Definitions.read_impl_interface st.context impl).implements.trait
               capability ->
          let interface = Definitions.read_impl_interface st.context impl in
          let self_ty =
            Monomorphic.ground st.context.monomorphic st.frame.code.substitution interface.for_type
          in
          let implementation =
            match st.frame.self_place with
            | _ when Memory_layout.has_zero_size st.context.env self_ty -> Lowered.Constant Null
            | Some self -> Lowered.Address { place = self; writable = true }
            | None -> raise_missing ()
          in
          let type_arguments =
            List.map
              (fun (generic : Types.generic) ->
                match Types.find_argument generic.generic st.frame.code.substitution with
                | Some argument ->
                    Monomorphic.ground_argument st.context.monomorphic Types.no_substitution
                      argument
                | None -> Definitions.raise_bug "an unbound parameter of %s" (Path.show impl))
              interface.impl_generics
          in
          lower_implementation_evidence st ~impl ~type_arguments ~implementation ~site:None
      | _ -> raise_missing ())

let pass_evidence (st : Lowering.state) ~site capability =
  extend_evidence st ~site capability (lookup_evidence st capability)

let pass_capabilities (st : Lowering.state) ~site capabilities =
  match capabilities with
  | [] -> Lowered.Constant Null
  | _ ->
      let table =
        Emit_c.Ir_builder.allocate_local st.builder (Capabilities (List.length capabilities))
      in
      Emit_c.Ir_builder.emit st.builder
        (Call
           {
             target = Intrinsic Capabilities_fill;
             arguments =
               Address { place = Lowered.make_local_place table; writable = true }
               :: List.concat_map
                    (fun capability ->
                      let name = Path.show capability in
                      [
                        Lowered.Constant (Bytes name);
                        Lowered.make_uint64_constant (String.length name);
                        pass_evidence st ~site capability;
                      ])
                    capabilities;
             result = Discarded;
           });
      Lowered.Address { place = Lowered.make_local_place table; writable = false }

let lower_nested_function (st : Lowering.state) ~(function_type : Ground.function_type)
    ~(output : Types.result option) ~(captures : (Lowered.place * Ground.ty) list)
    ~(body :
       Lowering.state ->
       captures:Lowered.place list ->
       (Lowered.place * Ground.mode * Ground.ty) list ->
       unit) destination =
  let index = !(st.nested) in
  incr st.nested;
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
  Emit_c.Ir_builder.build_nested st.builder ~index ~environment (fun builder ->
      let environment_local =
        Lowered.make_local_place (Emit_c.Ir_builder.allocate_local st.builder (Environment index))
      in
      List.iter
        (fun (name, place, _) ->
          Emit_c.Ir_builder.emit st.builder
            (Assign
               ( Lowered.project environment_local (Field name),
                 Use (Address { place; writable = false }) )))
        captured;
      Emit_c.Ir_builder.emit st.builder
        (Assign
           ( destination,
             Function_value
               {
                 code = Nested index;
                 environment = Some (Address { place = environment_local; writable = false });
               } ));
      let inner =
        Lowering.enter st.context ~nested:st.nested ~builder
          {
            st.frame with
            exit = None;
            code =
              (match output with
              | Some output -> { st.frame.code with result = output }
              | None -> st.frame.code);
          }
      in
      let environment_parameter =
        Emit_c.Ir_builder.allocate_local builder (Raw (Nullable_pointer Opaque))
      in
      Lowering.set_result_slot inner
        (Convention.classify_result st.context.env function_type.result);
      let parameter_places =
        List.map
          (fun ((mode : Ground.mode), ty) ->
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

let lower_indirect_call st ~(function_type : Ground.function_type) ~(value : Lowered.place) ~site
    (places : Lowered.place list) destination =
  let passed =
    List.concat
      (List.map2
         (fun ((mode : Ground.mode), ty) place ->
           let mode : Types.mode = match mode with Read -> Read | Mut -> Mut | Own -> Own in
           Option.to_list (pass st mode ty place))
         function_type.parameters places)
    @ [ pass_capabilities st ~site function_type.uses ]
  in
  let target =
    Lowered.Indirect
      {
        value = Copy value;
        signature = Convention.make_function_value_signature st.context.env function_type;
      }
  in
  Emit_c.Ir_builder.emit st.builder
    (Call
       {
         target;
         arguments = passed;
         result =
           Convention.make_destination
             (Convention.classify_result st.context.env function_type.result)
             destination;
       });
  if function_type.result = Never then Lowering.emit_unreachable_block st

let lower_call_through_any (st : Lowering.state) ~(any_type : Types.trait_reference) ~trait ~name
    ~receiver ~(any : Lowered.place) ~(arguments : (Types.mode * Ground.ty * Lowered.place) list)
    ?(lending = []) ~site destination =
  let index, signature = lookup_dynamic_method st.context trait name receiver in
  let slot =
    Drop_and_copy.compute_first_method_slot ~is_copyable:(is_copyable_any st.context any_type)
    + index
  in
  let c_signature, result, capabilities =
    make_any_entry_signature st.context ~any:any_type ~trait signature
  in
  let passed = List.filter_map (fun (mode, ty, place) -> pass st mode ty place) arguments in
  let evidence = List.map (pass_evidence st ~site) capabilities in
  let target =
    Lowered.Table_call
      {
        table = Copy (Lowered.project any (Field "vtable"));
        value = Copy (Lowered.project any (Field "value"));
        slot;
        signature = c_signature;
      }
  in
  Emit_c.Ir_builder.emit st.builder
    (Call
       {
         target;
         arguments = passed @ evidence @ lending;
         result = Convention.make_destination result destination;
       });
  if not c_signature.returns then Lowering.emit_unreachable_block st

let run_in_type_definition (st : Lowering.state) ~(source : Resolve.Names.key) (ty : Ground.ty)
    nested_function =
  let path, arguments =
    match ty with
    | Named { path; arguments } -> (path, arguments)
    | _ -> Definitions.raise_bug "defaults of %s" (Ground.to_string ty)
  in
  let interface = Interface.Definition.read_type_interface st.context.lookups.interface path in
  let caller = st.frame in
  st.frame <-
    {
      caller with
      code =
        {
          caller.code with
          definition = source.path;
          written = Some (Definitions.read_written st.context source);
          enclosing_impl = None;
          substitution = Definitions.bind interface.type_generics arguments;
        };
      self_place = None;
    };
  let result = nested_function () in
  st.frame <- caller;
  result

let begin_output st =
  let output = Lowering.allocate_temporary st Writing.output_ty in
  Emit_c.Ir_builder.emit st.builder (Assign (output, Storage.build_empty Writing.output_ty));
  output

let echo st place ty ~site =
  let output = begin_output st in
  Debug_output.emit_debug_call st.context.env st.builder
    ~output:(Address { place = output; writable = true })
    ty place;
  Emit_c.Ir_builder.emit st.builder
    (Echo
       {
         text = Copy (Storage.project_buffer output);
         length = Copy (Storage.project_length output);
         site;
       })

let lower_any_into (st : Lowering.state) ~any_ty ~inner_ty ~impl ~type_arguments
    ~(value : Lowered.place) destination =
  let box = Drop_and_copy.allocate_box st.context.drop_and_copy st.builder inner_ty in
  if not (Lowering.is_zero_size st inner_ty) then begin
    let typed =
      Emit_c.Ir_builder.allocate_local st.builder
        (Pointer { target = Value inner_ty; writable = true })
    in
    Emit_c.Ir_builder.emit st.builder
      (Assign (Lowered.make_local_place typed, Use (Copy (Lowered.make_local_place box))));
    Emit_c.Ir_builder.emit st.builder
      (Assign
         ( { root = Local typed; projections = [ Deref ] },
           Use (Lowering.make_owned_operand st value inner_ty) ))
  end;
  Emit_c.Ir_builder.emit st.builder
    (Assign
       ( destination,
         Build
           {
             ty = any_ty;
             variant = None;
             fields =
               [
                 ("value", Copy (Lowered.make_local_place box));
                 ("vtable", Constant (Symbol_address (Table (Any_table { impl; type_arguments }))));
               ];
           } ))

let lower_provided_evidence (st : Lowering.state) ~(implementation : Lowered.operand) ~site provides
    =
  List.map
    (fun (capability, impl, (arguments : Types.substitution)) ->
      let type_arguments =
        List.map
          (fun (generic : Types.generic) ->
            match Types.find_argument generic.generic arguments with
            | Some argument ->
                Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution
                  argument
            | None -> Definitions.raise_bug "an unbound parameter of %s" (Path.show impl))
          (Definitions.read_impl_interface st.context impl).impl_generics
      in
      (capability, lower_implementation_evidence st ~impl ~type_arguments ~implementation ~site))
    provides

let count_passed (signature : Types.signature) =
  let defaulted =
    List.length
      (List.filter
         (fun (parameter : Types.parameter_info) -> parameter.has_default)
         signature.parameters)
  in
  (1 lsl defaulted) - 1

let lower_item_call (st : Lowering.state) item ~(signature : Types.signature) ~substitution
    ~(arguments : (Types.mode * Ground.ty * Lowered.place) list) ?mask ?(lending = []) ~destination
    ~site () =
  let mask = match mask with Some mask -> mask | None -> count_passed signature in
  let c_signature, result =
    Definitions.make_c_signature st.context substitution
      ~parameters:(Definitions.list_interface_parameters signature)
      ~has_defaults:(Definitions.has_defaults signature)
      ~uses:signature.uses signature.output
  in
  let passed = List.filter_map (fun (mode, ty, place) -> pass st mode ty place) arguments in
  let mask =
    (if Definitions.has_defaults signature then
       [ Lowering.make_int_constant UInt64 (Z.of_int mask) ]
     else [])
    @ List.map (pass_evidence st ~site)
        (Definitions.list_evidence st.context substitution signature.uses)
  in
  let target = Lowered.Direct { function_ = Item item; signature = c_signature } in
  Emit_c.Ir_builder.emit st.builder
    (Call
       {
         target;
         arguments = passed @ mask @ lending;
         result = Convention.make_destination result destination;
       });
  if not c_signature.returns then Lowering.emit_unreachable_block st

type literal = Integer_value of Z.t | Float_value of float

let lower_literal st ty (literal : literal) : Lowered.operand =
  match (literal, Lowering.classify_scalar st ty) with
  | Integer_value value, Integer integer -> Lowering.make_int_constant integer value
  | Integer_value value, Character -> Constant (Character (Z.to_int value))
  | Float_value value, Float64 -> Constant (Float64 (Int64.bits_of_float value))
  | Float_value value, Float32 -> Constant (Float32 (Int32.bits_of_float value))
  | _ -> Definitions.raise_bug "a literal of type %s" (Ground.to_string ty)

let lower_literal_place st (ty : Ground.ty) text =
  let bytes : Lowered.operand = Constant (Bytes text) in
  let length = Lowered.make_uint64_constant (String.length text) in
  let build part_ty value =
    let built = Lowering.allocate_local st (Value part_ty) in
    Emit_c.Ir_builder.emit st.builder (Assign (built, value));
    built
  in
  let field, part =
    match (ty, Monomorphic.compute_shape st.context.monomorphic ty) with
    | Named { path; _ }, Record [ (field, Typed storage) ] when Well_known.is String path ->
        (field, build storage (Storage.build_storage storage ~buffer:bytes ~length ~capacity:length))
    | _, Record [ (field, Typed view) ] ->
        (field, build view (Storage.build_view view ~elements:bytes ~length))
    | _ -> Definitions.raise_bug "a string literal of type %s" (Ground.to_string ty)
  in
  build ty (Build { ty; variant = None; fields = [ (field, Copy part) ] })

let lower_owner_of_view (st : Lowering.state) ~(owner : Ground.ty) ~(view : Ground.ty)
    (viewed : Lowered.place) (destination : Lowered.place) =
  let storage_field, storage =
    match Monomorphic.compute_shape st.context.monomorphic owner with
    | Record [ (field, Typed storage) ] when Storage.match_storage_element storage <> None ->
        (field, storage)
    | _ -> Definitions.raise_bug "%s owns no storage" (Ground.to_string owner)
  in
  let elements =
    match Monomorphic.compute_shape st.context.monomorphic view with
    | Record [ (field, Typed elements) ] when Storage.match_view_element elements <> None ->
        Lowered.project viewed (Field field)
    | _ -> Definitions.raise_bug "%s views no storage" (Ground.to_string view)
  in
  let length : Lowered.operand = Copy (Storage.project_view_length elements) in
  let built = Lowering.allocate_local st (Value storage) in
  Emit_c.Ir_builder.emit st.builder
    (Assign
       ( built,
         Storage.build_storage storage
           ~buffer:(Copy (Storage.project_view_elements elements))
           ~length ~capacity:length ));
  Emit_c.Ir_builder.emit st.builder
    (Assign
       (destination, Build { ty = owner; variant = None; fields = [ (storage_field, Copy built) ] }))

let lower_static_constant (st : Lowering.state) path : Lowered.place =
  let ty = Interface.Definition.read_constant_type st.context.lookups.interface path in
  { root = Static { item = Constant path; ty = Lowering.ground st ty }; projections = [] }

let read_list_parts monomorphic ty =
  match Monomorphic.compute_shape monomorphic ty with
  | Record [ (field, Typed storage) ] -> (
      match Storage.match_storage_element storage with
      | Some element -> (field, storage, element)
      | None -> Definitions.raise_bug "%s is not a list" (Ground.to_string ty))
  | _ -> Definitions.raise_bug "%s is not a list" (Ground.to_string ty)

let lower_list_into (st : Lowering.state) ty destination ~site fills =
  let field, _, element = read_list_parts st.context.monomorphic ty in
  let storage_place = Lowered.project destination (Field field) in
  let lower operation arguments destination =
    ignore
      (Intrinsics.lower st.context.env st.builder st.context.types operation
         ~type_arguments:[ element ] arguments ~destination ~site
         ~trace:(Lowering.find_panic_trace st))
  in
  lower (Buffer Storage_with_capacity)
    [ Value (Lowered.make_uint64_constant (List.length fills)) ]
    (Some storage_place);
  List.iter
    (fun fill ->
      let value = Lowering.allocate_temporary st element in
      fill value;
      lower (Buffer Storage_push)
        [ Place storage_place; Value (Lowering.make_owned_operand st value element) ]
        None)
    fills

let lower_template_value (st : Lowering.state) template_ty literals ~site ~parts =
  let read_field_type ty name =
    match Monomorphic.compute_shape st.context.monomorphic ty with
    | Record fields -> (
        match List.assoc_opt name fields with
        | Some (Memory_layout.Typed ty) -> ty
        | _ -> Definitions.raise_bug "%s has no field %s" (Ground.to_string ty) name)
    | _ -> Definitions.raise_bug "%s is not a record" (Ground.to_string ty)
  in
  let read_element_type list_ty =
    let _, _, element = read_list_parts st.context.monomorphic list_ty in
    element
  in
  let literals_ty = read_field_type template_ty "literals" in
  let parts_ty = read_field_type template_ty "parts" in
  let literal_ty = read_element_type literals_ty in
  let slice_ty = read_field_type literal_ty "text" in
  let built = Lowering.allocate_temporary st template_ty in
  lower_list_into st literals_ty
    (Lowered.project built (Field "literals"))
    ~site
    (List.map
       (fun text value ->
         Emit_c.Ir_builder.emit st.builder
           (Assign
              ( value,
                Build
                  {
                    ty = literal_ty;
                    variant = None;
                    fields = [ ("text", Copy (lower_literal_place st slice_ty text)) ];
                  } )))
       literals);
  lower_list_into st parts_ty (Lowered.project built (Field "parts")) ~site parts;
  built

let pull_loop st ~(option : Ground.ty) ~(call_next : Lowered.place -> unit)
    ~(body : Lowered.place -> unit) =
  Lowering.run_in_scope st (fun () ->
      let next = Lowering.allocate_local st (Value option) in
      let depth = List.length st.scopes in
      let test = Emit_c.Ir_builder.allocate_block st.builder
      and inside = Emit_c.Ir_builder.allocate_block st.builder
      and after = Emit_c.Ir_builder.allocate_block st.builder in
      Emit_c.Ir_builder.finish st.builder (Goto test);
      Emit_c.Ir_builder.start st.builder test;
      call_next next;
      let more = Emit_c.Ir_builder.allocate_local st.builder (Raw Bool) in
      Emit_c.Ir_builder.emit st.builder
        (Assign (Lowered.make_local_place more, Is_variant (next, "Some")));
      Emit_c.Ir_builder.branch st.builder
        (Copy (Lowered.make_local_place more))
        ~yes:inside ~no:after;
      Emit_c.Ir_builder.start st.builder inside;
      Lowering.run_in_scope st (fun () ->
          Lowering.run_in_loop st ~continue_:test ~break_:after ~depth (fun () ->
              body (Lowered.project next (Variant_field { variant = "Some"; field = "value" }))));
      Emit_c.Ir_builder.finish st.builder (Goto test);
      Emit_c.Ir_builder.start st.builder after)
