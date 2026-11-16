let resolve_impl (context : Definitions.context) substitution ~(trait : Types.trait_reference)
    ~self_type ~(evidence : Core.evidence) =
  let substitute = Types.substitute substitution in
  let impl, arguments =
    match evidence with
    | Impl { impl; arguments } ->
        ( impl,
          List.map
            (fun (parameter, argument) ->
              (parameter, Types.substitute_argument substitution argument))
            arguments )
    | Bound -> (
        let self = context.monomorphic.normalize (substitute self_type) in
        match
          Interface.Impls.implements context.lookups.interface ~bounds:Interface.Impls.no_bounds
            self
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
        | _ -> Definitions.bug "no impl of %s for %s" (Types.show_trait trait) (Types.show self))
    | Dynamic -> Definitions.bug "a call through any, which reaches no one instance"
  in
  let impl_interface =
    match Interface.Definition.read_impl_interface context.lookups.interface impl with
    | Some position -> position
    | None -> Definitions.bug "no interface for %s" (Path.show impl)
  in
  let impl_arguments =
    List.map
      (fun (generic : Types.generic) ->
        match List.assoc_opt generic.generic arguments with
        | Some argument -> Monomorphic.ground_argument context.monomorphic [] argument
        | None -> Definitions.bug "the impl's parameter %s is not bound" generic.generic.name)
      impl_interface.impl_generics
  in
  (impl, impl_arguments)

let trait_method_key context substitution ~(trait : Types.trait_reference) ~name ~receiver
    ~self_type ~type_arguments ~(evidence : Core.evidence) =
  let impl, impl_arguments = resolve_impl context substitution ~trait ~self_type ~evidence in
  Instance.Code
    {
      path = Method { owner = impl; name; receiver };
      type_arguments =
        impl_arguments
        @ List.map (Monomorphic.ground_argument context.monomorphic substitution) type_arguments;
    }

let operand_as st (mode : Types.mode) ty (place : Lowered.place) (passed : Lowered.ty option) =
  match passed with
  | None -> None
  | Some (Pointer _) when mode = Types.Own ->
      ignore (Lowering.moved st place);
      Some (Lowered.Moved_address place)
  | Some (Pointer { writable; _ }) -> Some (Lowered.Address { place; writable })
  | Some _ -> (
      match mode with Own -> Some (Lowering.owned st place ty) | Read | Mut -> Some (Copy place))

let pass st (mode : Types.mode) ty place =
  operand_as st mode ty place (Convention.parameter st.context.env (Monomorphic.mode mode) ty)

let method_slot (context : Definitions.context) ~owner ~first ~missing
    (methods : Types.trait_method list) name =
  match
    List.find_index
      (fun (trait_method : Types.trait_method) -> trait_method.method_name = name)
      methods
  with
  | Some index ->
      ( first + index,
        Interface.Definition.read_method_signature context.lookups.interface ~owner
          (List.nth methods index) )
  | None -> missing ()

let capability_method (context : Definitions.context) capability name =
  let interface =
    match Interface.Definition.read_trait_interface context.lookups.interface capability with
    | Some position -> position
    | None -> Definitions.bug "no interface for %s" (Path.show capability)
  in
  method_slot context ~owner:capability ~first:0 interface.methods name ~missing:(fun () ->
      Definitions.bug "%s has no method %s" (Path.show capability) name)

let entry_signature context (signature : Types.signature) =
  let entry, result =
    Definitions.c_signature context []
      ~parameters:(Definitions.interface_parameters { signature with receiver = None })
      ~has_defaults:false signature.output
  in
  ({ entry with parameters = Convention.evidence :: entry.parameters }, result)

let callable_through_any (context : Definitions.context) trait (trait_method : Types.trait_method) =
  trait_method.method_receiver <> Static
  && Interface.Impls.classify_through_any context.lookups.interface ~trait trait_method = Callable

let any_methods (context : Definitions.context) trait =
  match Interface.Definition.read_trait_interface context.lookups.interface trait with
  | Some position -> List.filter (callable_through_any context trait) position.methods
  | None -> Definitions.bug "no interface for %s" (Path.show trait)

let dynamic_method context trait name =
  method_slot context ~owner:trait ~first:0 (any_methods context trait) name ~missing:(fun () ->
      Definitions.bug "%s cannot be called through any" name)

let is_copyable_any (context : Definitions.context) (any : Types.trait_reference) =
  Interface.Impls.is_copyable context.lookups.interface ~bounds:Interface.Impls.no_bounds
    (Types.Any any)

let any_substitution (context : Definitions.context) ~(any : Types.trait_reference) trait :
    Types.substitution =
  match Interface.Definition.read_trait_interface context.lookups.interface trait with
  | Some interface ->
      let reference =
        if Path.equal trait any.trait then any
        else
          match
            List.find_opt
              (fun (bound : Types.trait_reference) -> Path.equal bound.trait trait)
              (Interface.Properties.list_bound_closure context.lookups.interface
                 ~self:(Types.Any any) any)
          with
          | Some bound -> bound
          | None ->
              Definitions.bug "%s is not a trait of %s" (Path.show trait)
                (Types.show (Types.Any any))
      in
      Interface.Properties.make_trait_substitution interface ~self:(Types.Any any) reference
  | None -> Definitions.bug "no interface for %s" (Path.show trait)

let any_entry_signature context ~any ~trait (signature : Types.signature) =
  let substitution = any_substitution context ~any trait in
  let entry, result =
    Definitions.c_signature context substitution
      ~parameters:(Definitions.interface_parameters { signature with receiver = None })
      ~has_defaults:false ~uses:signature.uses signature.output
  in
  ( { entry with parameters = Lowered.Raw (Pointer Opaque) :: entry.parameters },
    result,
    Definitions.evidence_for context substitution signature.uses )

let implementation_evidence (st : Lowering.state) ~impl ~type_arguments ~implementation =
  let outer =
    List.map
      (fun captured ->
        match List.find_opt (fun (path, _) -> Path.equal path captured) st.evidence with
        | Some (_, operand) -> operand
        | None -> Definitions.bug "no evidence for %s here" (Path.show captured))
      (Definitions.evidence_for st.context [] (Definitions.impl_interface st.context impl).impl_uses)
  in
  let slot = Emit_c.Builder.local st.builder (Evidence (List.length outer)) in
  Emit_c.Builder.emit st.builder
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

let evidence_of (st : Lowering.state) capability =
  match List.find_opt (fun (path, _) -> Path.equal path capability) st.evidence with
  | Some (_, operand) -> operand
  | None -> (
      let missing () = Definitions.bug "no evidence for %s here" (Path.show capability) in
      match st.frame.code.enclosing_impl with
      | Some impl
        when Path.equal (Definitions.impl_interface st.context impl).implements.trait capability ->
          let interface = Definitions.impl_interface st.context impl in
          let self_ty =
            Monomorphic.ground st.context.monomorphic st.frame.code.substitution interface.for_type
          in
          let implementation =
            match st.frame.self_place with
            | _ when Memory_layout.has_zero_size st.context.env self_ty -> Lowered.Constant Null
            | Some self -> Lowered.Address { place = self; writable = true }
            | None -> missing ()
          in
          let type_arguments =
            List.map
              (fun (generic : Types.generic) ->
                match List.assoc_opt generic.generic st.frame.code.substitution with
                | Some argument -> Monomorphic.ground_argument st.context.monomorphic [] argument
                | None -> Definitions.bug "an unbound parameter of %s" (Path.show impl))
              interface.impl_generics
          in
          implementation_evidence st ~impl ~type_arguments ~implementation
      | _ -> missing ())

let nested_function (st : Lowering.state) ~(function_type : Ground.function_type)
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
  Emit_c.Builder.build_nested st.builder ~index ~environment (fun builder ->
      let environment_local =
        Lowered.make_local_place (Emit_c.Builder.local st.builder (Environment index))
      in
      List.iter
        (fun (name, place, _) ->
          Emit_c.Builder.emit st.builder
            (Assign
               ( Lowered.project environment_local (Field name),
                 Use (Address { place; writable = false }) )))
        captured;
      Emit_c.Builder.emit st.builder
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
        Emit_c.Builder.local builder ~name:"environment" (Raw (Nullable_pointer Opaque))
      in
      Lowering.result_slot inner (Convention.result st.context.env function_type.result);
      let parameter_places =
        List.map
          (fun ((mode : Ground.mode), ty) ->
            (Lowering.parameter inner ~in_scope:false ~owned:(mode = Own) mode ty, mode, ty))
          function_type.parameters
      in
      let evidence = Lowering.evidence_parameters inner function_type.uses in
      let environment_pointer =
        Emit_c.Builder.local builder (Pointer { target = Environment index; writable = false })
      in
      Emit_c.Builder.start builder (Emit_c.Builder.block builder);
      Emit_c.Builder.emit builder
        (Assign
           ( Lowered.make_local_place environment_pointer,
             Use (Copy (Lowered.make_local_place environment_parameter)) ));
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
        ~rest:(List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places @ evidence)
        ())

let call_indirect st ~(function_type : Ground.function_type) ~(value : Lowered.place)
    (places : Lowered.place list) destination =
  let passed =
    List.concat
      (List.map2
         (fun ((mode : Ground.mode), ty) place ->
           let mode : Types.mode = match mode with Read -> Read | Mut -> Mut | Own -> Own in
           Option.to_list (pass st mode ty place))
         function_type.parameters places)
    @ List.map (evidence_of st) function_type.uses
  in
  let target =
    Lowered.Indirect
      { value = Copy value; signature = Convention.function_value st.context.env function_type }
  in
  Emit_c.Builder.emit st.builder
    (Call
       {
         target;
         arguments = passed;
         result =
           Convention.destination
             (Convention.result st.context.env function_type.result)
             destination;
       });
  if function_type.result = Never then Lowering.unreachable_block st

let call_through_any (st : Lowering.state) ~(any_type : Types.trait_reference) ~trait ~name
    ~(any : Lowered.place) ~(arguments : (Types.mode * Ground.ty * Lowered.place) list)
    ?(lending = []) destination =
  let index, signature = dynamic_method st.context trait name in
  let slot =
    Drop_and_copy.first_method_slot ~is_copyable:(is_copyable_any st.context any_type) + index
  in
  let c_signature, result, capabilities =
    any_entry_signature st.context ~any:any_type ~trait signature
  in
  let passed = List.filter_map (fun (mode, ty, place) -> pass st mode ty place) arguments in
  let evidence = List.map (evidence_of st) capabilities in
  let target =
    Lowered.Table_call
      {
        table = Copy (Lowered.project any (Field "vtable"));
        value = Copy (Lowered.project any (Field "value"));
        slot;
        signature = c_signature;
      }
  in
  Emit_c.Builder.emit st.builder
    (Call
       {
         target;
         arguments = passed @ evidence @ lending;
         result = Convention.destination result destination;
       });
  if not c_signature.returns then Lowering.unreachable_block st

let in_type_definition (st : Lowering.state) ~(source : Resolve.Names.key) (ty : Ground.ty)
    nested_function =
  let path, arguments =
    match ty with
    | Named { path; arguments } -> (path, arguments)
    | _ -> Definitions.bug "defaults of %s" (Ground.to_string ty)
  in
  let interface =
    match Interface.Definition.read_type_interface st.context.lookups.interface path with
    | Some position -> position
    | None -> Definitions.bug "no interface for %s" (Path.show path)
  in
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
  let output = Lowering.temporary st Writing.output_ty in
  Emit_c.Builder.emit st.builder (Assign (output, Storage.build_empty Writing.output_ty));
  output

let echo st place ty ~site =
  let output = begin_output st in
  Debug_output.debug_call st.context.env st.builder
    ~output:(Address { place = output; writable = true })
    ty place;
  Emit_c.Builder.emit st.builder
    (Echo
       {
         text = Copy (Storage.project_buffer output);
         length = Copy (Storage.project_length output);
         site;
       })

let any_into (st : Lowering.state) ~any_ty ~inner_ty ~impl ~type_arguments ~(value : Lowered.place)
    destination =
  let box = Drop_and_copy.box st.context.drop_and_copy st.builder inner_ty in
  if not (Lowering.is_zero_size st inner_ty) then begin
    let typed =
      Emit_c.Builder.local st.builder (Pointer { target = Value inner_ty; writable = true })
    in
    Emit_c.Builder.emit st.builder
      (Assign (Lowered.make_local_place typed, Use (Copy (Lowered.make_local_place box))));
    Emit_c.Builder.emit st.builder
      (Assign
         ({ root = Local typed; projections = [ Deref ] }, Use (Lowering.owned st value inner_ty)))
  end;
  Emit_c.Builder.emit st.builder
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

let provided_evidence (st : Lowering.state) ~(implementation : Lowered.operand) provides =
  List.map
    (fun (capability, impl, (arguments : Types.substitution)) ->
      let type_arguments =
        List.map
          (fun (generic : Types.generic) ->
            match List.assoc_opt generic.generic arguments with
            | Some argument ->
                Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution
                  argument
            | None -> Definitions.bug "an unbound parameter of %s" (Path.show impl))
          (Definitions.impl_interface st.context impl).impl_generics
      in
      (capability, implementation_evidence st ~impl ~type_arguments ~implementation))
    provides

let all_passed (signature : Types.signature) =
  let defaulted =
    List.length
      (List.filter
         (fun (parameter : Types.parameter_info) -> parameter.has_default)
         signature.parameters)
  in
  (1 lsl defaulted) - 1

let call_instance (st : Lowering.state) key ~(signature : Types.signature) ~substitution
    ~(arguments : (Types.mode * Ground.ty * Lowered.place) list) ?mask ?(lending = []) ~destination
    () =
  let mask = match mask with Some mask -> mask | None -> all_passed signature in
  let c_signature, result =
    Definitions.c_signature st.context substitution
      ~parameters:(Definitions.interface_parameters signature)
      ~has_defaults:(Definitions.has_defaults signature)
      ~uses:signature.uses signature.output
  in
  let passed = List.filter_map (fun (mode, ty, place) -> pass st mode ty place) arguments in
  let mask =
    (if Definitions.has_defaults signature then [ Lowering.constant_int UInt64 (Z.of_int mask) ]
     else [])
    @ List.map (evidence_of st) (Definitions.evidence_for st.context substitution signature.uses)
  in
  let target = Lowered.Direct { function_ = Instance key; signature = c_signature } in
  Emit_c.Builder.emit st.builder
    (Call
       {
         target;
         arguments = passed @ mask @ lending;
         result = Convention.destination result destination;
       });
  if not c_signature.returns then Lowering.unreachable_block st

type literal = Integer_value of Z.t | Float_value of float

let constant_of st ty (literal : literal) : Lowered.operand =
  match (literal, Lowering.scalar_of st ty) with
  | Integer_value value, Integer integer -> Lowering.constant_int integer value
  | Integer_value value, Character -> Constant (Character (Z.to_int value))
  | Float_value value, Float64 -> Constant (Float64 (Int64.bits_of_float value))
  | Float_value value, Float32 -> Constant (Float32 (Int32.bits_of_float value))
  | _ -> Definitions.bug "a literal of type %s" (Ground.to_string ty)

let literal_place st (ty : Ground.ty) text =
  let bytes : Lowered.operand = Constant (Bytes text) in
  let length = Lowered.make_uint64_constant (String.length text) in
  let build part_ty value =
    let built = Lowering.held st (Value part_ty) in
    Emit_c.Builder.emit st.builder (Assign (built, value));
    built
  in
  let field, part =
    match (ty, Monomorphic.shape st.context.monomorphic ty) with
    | Named { path; _ }, Record [ (field, Typed storage) ] when Well_known.is String path ->
        (field, build storage (Storage.build_storage storage ~buffer:bytes ~length ~capacity:length))
    | _, Record [ (field, Typed view) ] ->
        (field, build view (Storage.build_view view ~elements:bytes ~length))
    | _ -> Definitions.bug "a string literal of type %s" (Ground.to_string ty)
  in
  build ty (Build { ty; variant = None; fields = [ (field, Copy part) ] })

let static_constant (st : Lowering.state) path : Lowered.place =
  match Interface.Definition.read_constant_type st.context.lookups.interface path with
  | Some ty ->
      { root = Static { key = Constant path; ty = Lowering.ground st ty }; projections = [] }
  | None -> Definitions.bug "no type for the constant %s" (Path.show path)

let list_parts monomorphic ty =
  match Monomorphic.shape monomorphic ty with
  | Record [ (field, Typed storage) ] -> (
      match Storage.match_storage_element storage with
      | Some element -> (field, storage, element)
      | None -> Definitions.bug "%s is not a list" (Ground.to_string ty))
  | _ -> Definitions.bug "%s is not a list" (Ground.to_string ty)

let list_of (st : Lowering.state) ty destination ~site fills =
  let field, _, element = list_parts st.context.monomorphic ty in
  let storage_place = Lowered.project destination (Field field) in
  let lower operation arguments destination =
    ignore
      (Intrinsics.lower ~checks:st.context.checks st.context.env st.builder st.context.types
         operation ~type_arguments:[ element ] arguments ~destination ~site)
  in
  lower Storage_with_capacity
    [ Value (Lowered.make_uint64_constant (List.length fills)) ]
    (Some storage_place);
  List.iter
    (fun fill ->
      let value = Lowering.temporary st element in
      fill value;
      lower Storage_push [ Place storage_place; Value (Lowering.owned st value element) ] None)
    fills

let template_value (st : Lowering.state) template_ty literals ~site ~parts =
  let field_type ty name =
    match Monomorphic.shape st.context.monomorphic ty with
    | Record fields -> (
        match List.assoc_opt name fields with
        | Some (Memory_layout.Typed ty) -> ty
        | _ -> Definitions.bug "%s has no field %s" (Ground.to_string ty) name)
    | _ -> Definitions.bug "%s is not a record" (Ground.to_string ty)
  in
  let element list_ty =
    let _, _, element = list_parts st.context.monomorphic list_ty in
    element
  in
  let literals_ty = field_type template_ty "literals" in
  let parts_ty = field_type template_ty "parts" in
  let literal_ty = element literals_ty in
  let slice_ty = field_type literal_ty "text" in
  let built = Lowering.temporary st template_ty in
  list_of st literals_ty
    (Lowered.project built (Field "literals"))
    ~site
    (List.map
       (fun text value ->
         Emit_c.Builder.emit st.builder
           (Assign
              ( value,
                Build
                  {
                    ty = literal_ty;
                    variant = None;
                    fields = [ ("text", Copy (literal_place st slice_ty text)) ];
                  } )))
       literals);
  list_of st parts_ty (Lowered.project built (Field "parts")) ~site parts;
  built

let pull_loop st ~(option : Ground.ty) ~(call_next : Lowered.place -> unit)
    ~(body : Lowered.place -> unit) =
  Lowering.in_scope st (fun () ->
      let next = Lowering.held st (Value option) in
      let depth = List.length st.scopes in
      let test = Emit_c.Builder.block st.builder
      and inside = Emit_c.Builder.block st.builder
      and after = Emit_c.Builder.block st.builder in
      Emit_c.Builder.finish st.builder (Goto test);
      Emit_c.Builder.start st.builder test;
      call_next next;
      let more = Emit_c.Builder.local st.builder (Raw Bool) in
      Emit_c.Builder.emit st.builder
        (Assign (Lowered.make_local_place more, Is_variant (next, "Some")));
      Emit_c.Builder.branch st.builder (Copy (Lowered.make_local_place more)) ~yes:inside ~no:after;
      Emit_c.Builder.start st.builder inside;
      Lowering.in_scope st (fun () ->
          Lowering.looping st ~continue_:test ~break_:after ~depth (fun () ->
              body (Lowered.project next (Variant_field { variant = "Some"; field = "value" }))));
      Emit_c.Builder.finish st.builder (Goto test);
      Emit_c.Builder.start st.builder after)
