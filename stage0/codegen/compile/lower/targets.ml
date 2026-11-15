open Definitions
open Lowering
open Emit_c.Builder

let resolve_impl context substitution ~(trait : Types.trait_reference) ~self_type
    ~(evidence : Core.evidence) =
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
        | _ -> bug "no impl of %s for %s" (Types.show_trait trait) (Types.show self))
    | Dynamic -> bug "a call through any, which reaches no one instance"
  in
  let impl_interface =
    match Interface.Impls.impl_interface context.lookups.interface impl with
    | Some position -> position
    | None -> bug "no interface for %s" (Path.show impl)
  in
  let impl_arguments =
    List.map
      (fun (generic : Types.generic) ->
        match List.assoc_opt generic.generic arguments with
        | Some argument -> Monomorphic.ground_argument context.monomorphic [] argument
        | None -> bug "the impl's parameter %s is not bound" generic.generic.name)
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
      ignore (moved st place);
      Some (Lowered.Moved_address place)
  | Some (Pointer { writable; _ }) -> Some (Lowered.Address { place; writable })
  | Some _ -> ( match mode with Own -> Some (owned st place ty) | Read | Mut -> Some (Copy place))

let pass st (mode : Types.mode) ty place =
  operand_as st mode ty place (Convention.parameter st.context.env (Monomorphic.mode mode) ty)

let method_slot context ~owner ~first ~missing (methods : Types.trait_method list) name =
  match
    List.find_index
      (fun (trait_method : Types.trait_method) -> trait_method.method_name = name)
      methods
  with
  | Some index ->
      ( first + index,
        Interface.Definition.method_signature context.lookups.interface ~owner
          (List.nth methods index) )
  | None -> missing ()

let capability_method context capability name =
  let interface =
    match Interface.Definition.trait_interface context.lookups.interface capability with
    | Some position -> position
    | None -> bug "no interface for %s" (Path.show capability)
  in
  method_slot context ~owner:capability ~first:0 interface.methods name ~missing:(fun () ->
      bug "%s has no method %s" (Path.show capability) name)

let entry_signature context (signature : Types.signature) =
  let entry, result =
    c_signature context []
      ~parameters:(interface_parameters { signature with receiver = None })
      ~has_defaults:false signature.output
  in
  ({ entry with parameters = Convention.evidence :: entry.parameters }, result)

let callable_through_any context trait (trait_method : Types.trait_method) =
  trait_method.method_receiver <> Static
  && Interface.Impls.through_any context.lookups.interface ~trait trait_method = Callable

let is_copyable_any context (any : Types.trait_reference) =
  Interface.Properties.has context.lookups.interface
    ~bounds:(fun _ -> [])
    ~normalize:context.monomorphic.normalize Interface.Properties.Copyable (Types.Any any)

type any_method = {
  trait : Types.trait_reference;
  trait_method : Types.trait_method;
  signature : Types.signature;
  substitution : Types.substitution;
}

type any_slot = Drop_slot | Copy_slot | Method_slot of any_method

let lay_out_any_vtable context (any : Types.trait_reference) =
  let traits =
    List.fold_left
      (fun traits (bound : Types.trait_reference) ->
        if
          List.exists
            (fun (trait : Types.trait_reference) -> Path.equal trait.trait bound.trait)
            traits
        then traits
        else traits @ [ bound ])
      []
      (Interface.Properties.bound_closure context.lookups.interface ~self:(Types.Any any) any)
  in
  let lay_out_methods (trait : Types.trait_reference) =
    match Interface.Definition.trait_interface context.lookups.interface trait.trait with
    | Some interface ->
        let substitution =
          Interface.Properties.trait_substitution interface ~self:(Types.Any any) trait
        in
        List.filter_map
          (fun trait_method ->
            if callable_through_any context trait.trait trait_method then
              Some
                (Method_slot
                   {
                     trait;
                     trait_method;
                     signature =
                       Interface.Definition.method_signature context.lookups.interface
                         ~owner:trait.trait trait_method;
                     substitution;
                   })
            else None)
          interface.methods
    | None -> bug "no interface for %s" (Path.show trait.trait)
  in
  (Drop_slot :: (if is_copyable_any context any then [ Copy_slot ] else []))
  @ List.concat_map lay_out_methods traits

let find_any_method context ~(any : Types.trait_reference) trait name =
  match
    List.find_mapi
      (fun slot -> function
        | Method_slot any_method
          when Path.equal any_method.trait.trait trait && any_method.trait_method.method_name = name
          ->
            Some (slot, any_method)
        | Drop_slot | Copy_slot | Method_slot _ -> None)
      (lay_out_any_vtable context any)
  with
  | Some found -> found
  | None -> bug "%s cannot be called through any %s" name (Path.show any.trait)

let make_any_entry_signature context ~substitution (signature : Types.signature) =
  let entry, result =
    c_signature context substitution
      ~parameters:(interface_parameters { signature with receiver = None })
      ~has_defaults:false ~uses:signature.uses signature.output
  in
  ( { entry with parameters = Lowered.Raw (Pointer Opaque) :: entry.parameters },
    result,
    evidence_for context substitution signature.uses )

let implementation_evidence st ~impl ~type_arguments ~implementation =
  let outer =
    List.map
      (fun captured ->
        match List.find_opt (fun (path, _) -> Path.equal path captured) st.evidence with
        | Some (_, operand) -> operand
        | None -> bug "no evidence for %s here" (Path.show captured))
      (evidence_for st.context [] (impl_interface st.context impl).impl_uses)
  in
  let slot = local st.builder (Evidence (List.length outer)) in
  emit st.builder
    (Call
       {
         target = Intrinsic Evidence_fill;
         arguments =
           Address { place = at slot; writable = true }
           :: implementation
           :: Constant (Symbol_address (Table { impl; type_arguments }))
           :: outer;
         result = Discarded;
       });
  Lowered.Address { place = at slot; writable = false }

let evidence_of st capability =
  match List.find_opt (fun (path, _) -> Path.equal path capability) st.evidence with
  | Some (_, operand) -> operand
  | None -> (
      let missing () = bug "no evidence for %s here" (Path.show capability) in
      match st.frame.code.enclosing_impl with
      | Some impl when Path.equal (impl_interface st.context impl).implements.trait capability ->
          let interface = impl_interface st.context impl in
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
                | None -> bug "an unbound parameter of %s" (Path.show impl))
              interface.impl_generics
          in
          implementation_evidence st ~impl ~type_arguments ~implementation
      | _ -> missing ())

let nested_function st ~(function_type : Ground.function_type) ~(output : Types.result option)
    ~(captures : (Lowered.place * Ground.ty) list)
    ~(body :
       state ->
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
  let builder = Emit_c.Builder.nested st.builder ~index ~environment in
  let environment_local = at (local st.builder (Environment index)) in
  List.iter
    (fun (name, place, _) ->
      emit st.builder
        (Assign (environment_local / Field name, Use (Address { place; writable = false }))))
    captured;
  emit st.builder
    (Assign
       ( destination,
         Function_value
           {
             code = Nested index;
             environment = Some (Address { place = environment_local; writable = false });
           } ));
  let inner =
    enter st.context ~nested:st.nested ~builder
      {
        st.frame with
        exit = None;
        code =
          (match output with
          | Some output -> { st.frame.code with result = output }
          | None -> st.frame.code);
      }
  in
  let environment_parameter = local builder ~name:"environment" (Raw (Nullable_pointer Opaque)) in
  let result_ty =
    match function_type.result with Returns ty -> ty | _ -> bug "a lambda that lends"
  in
  result_slot inner (Convention.result st.context.env result_ty);
  let parameter_places =
    List.map
      (fun ((mode : Ground.mode), ty) ->
        (parameter inner ~in_scope:false ~owned:(mode = Own) mode ty, mode, ty))
      function_type.parameters
  in
  let evidence = evidence_parameters inner function_type.uses in
  let environment_pointer =
    local builder (Pointer { target = Environment index; writable = false })
  in
  start builder (block builder);
  emit builder (Assign (at environment_pointer, Use (Copy (at environment_parameter))));
  body inner
    ~captures:
      (List.map
         (fun (name, _, _) ->
           { Lowered.root = Local environment_pointer; projections = [ Deref; Field name; Deref ] })
         captured)
    (List.map (fun ((_, place), mode, ty) -> (place, mode, ty)) parameter_places);
  finish_function inner ~first:[ environment_parameter ]
    ~rest:(List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places @ evidence)
    ()

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
  match function_type.result with
  | Returns ty ->
      emit st.builder
        (Call
           {
             target;
             arguments = passed;
             result = Convention.(destination (result st.context.env ty)) destination;
           });
      if ty = Never then unreachable_block st
  | Lends _ -> bug "a function value that lends"

let call_through_any st ~(any_type : Types.trait_reference) ~trait ~name ~(any : Lowered.place)
    ~(arguments : (Types.mode * Ground.ty * Lowered.place) list) ?(lending = []) destination =
  let slot, any_method = find_any_method st.context ~any:any_type trait name in
  let c_signature, result, capabilities =
    make_any_entry_signature st.context ~substitution:any_method.substitution any_method.signature
  in
  let passed = List.filter_map (fun (mode, ty, place) -> pass st mode ty place) arguments in
  let evidence = List.map (evidence_of st) capabilities in
  let target =
    Lowered.Table_call
      {
        table = Copy (any / Field "vtable");
        value = Copy (any / Field "value");
        slot;
        signature = c_signature;
      }
  in
  emit st.builder
    (Call
       {
         target;
         arguments = passed @ evidence @ lending;
         result = Convention.destination result destination;
       });
  if not c_signature.returns then unreachable_block st

let in_type_definition st (ty : Ground.ty) nested_function =
  let path, arguments =
    match ty with
    | Named { path; arguments } -> (path, arguments)
    | _ -> bug "defaults of %s" (Ground.to_string ty)
  in
  let key = key_of st.context path in
  let interface =
    match Interface.Definition.type_interface st.context.lookups.interface path with
    | Some position -> position
    | None -> bug "no interface for %s" (Path.show path)
  in
  let caller = st.frame in
  st.frame <-
    {
      caller with
      code =
        {
          caller.code with
          definition_key = key;
          anchor = path;
          enclosing_impl = None;
          text = text_of st.context key;
          substitution = bind interface.type_generics arguments;
        };
      self_place = None;
    };
  let result = nested_function () in
  st.frame <- caller;
  result

let begin_output st =
  let output = temporary st Writing.output_ty in
  emit st.builder (Assign (output, Storage.empty Writing.output_ty));
  output

let echo st place ty ~site =
  let output = begin_output st in
  Debug_output.debug_call st.context.env st.builder
    ~output:(Address { place = output; writable = true })
    ty place;
  emit st.builder
    (Echo { text = Copy (Storage.buffer output); length = Copy (Storage.length output); site })

let any_into st ~any_ty ~inner_ty ~impl ~type_arguments ~(value : Lowered.place) destination =
  let box = Drop_and_copy.box st.context.drop_and_copy st.builder inner_ty in
  if not (is_zero_size st inner_ty) then begin
    let typed = local st.builder (Pointer { target = Value inner_ty; writable = true }) in
    emit st.builder (Assign (at typed, Use (Copy (at box))));
    emit st.builder
      (Assign ({ root = Local typed; projections = [ Deref ] }, Use (owned st value inner_ty)))
  end;
  emit st.builder
    (Assign
       ( destination,
         Build
           {
             ty = any_ty;
             variant = None;
             fields =
               [
                 ("value", Copy (at box));
                 ("vtable", Constant (Symbol_address (Any_table { impl; type_arguments })));
               ];
           } ))

let provided_evidence st ~(implementation : Lowered.operand) provides =
  List.map
    (fun (capability, impl, (arguments : Types.substitution)) ->
      let type_arguments =
        List.map
          (fun (generic : Types.generic) ->
            match List.assoc_opt generic.generic arguments with
            | Some argument ->
                Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution
                  argument
            | None -> bug "an unbound parameter of %s" (Path.show impl))
          (impl_interface st.context impl).impl_generics
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

let call_instance st key ~(signature : Types.signature) ~substitution
    ~(arguments : (Types.mode * Ground.ty * Lowered.place) list) ?mask ?(lending = []) ~destination
    () =
  let mask = match mask with Some mask -> mask | None -> all_passed signature in
  let c_signature, result =
    c_signature st.context substitution ~parameters:(interface_parameters signature)
      ~has_defaults:(has_defaults signature) ~uses:signature.uses signature.output
  in
  let passed = List.filter_map (fun (mode, ty, place) -> pass st mode ty place) arguments in
  let mask =
    (if has_defaults signature then [ constant_int UInt64 (Z.of_int mask) ] else [])
    @ List.map (evidence_of st) (evidence_for st.context substitution signature.uses)
  in
  let target = Lowered.Direct { function_ = Instance key; signature = c_signature } in
  emit st.builder
    (Call
       {
         target;
         arguments = passed @ mask @ lending;
         result = Convention.destination result destination;
       });
  if not c_signature.returns then unreachable_block st

type literal = Integer_value of Z.t | Float_value of float

let constant_of st ty (literal : literal) : Lowered.operand =
  match (literal, scalar_of st ty) with
  | Integer_value value, Integer integer -> constant_int integer value
  | Integer_value value, Character -> Constant (Character (Z.to_int value))
  | Float_value value, Float64 -> Constant (Float64 (Int64.bits_of_float value))
  | Float_value value, Float32 -> Constant (Float32 (Int32.bits_of_float value))
  | _ -> bug "a literal of type %s" (Ground.to_string ty)

let string_literal st (ty : Ground.ty) text ~(destination : Lowered.place) =
  let length = constant_uint64 (String.length text) in
  let build field operand =
    emit st.builder
      (Assign (destination, Build { ty; variant = None; fields = [ (field, operand) ] }))
  in
  match (ty, Monomorphic.shape st.context.monomorphic ty) with
  | Named { path; _ }, Record [ (field, Typed storage) ] when Well_known.is String path ->
      let bytes = temporary st storage in
      emit st.builder
        (Assign (bytes, Storage.static storage ~elements:(Constant (Bytes text)) ~length));
      build field (moved st bytes)
  | _, Record [ (field, Typed view) ] ->
      let bytes = temporary st view in
      emit st.builder (Assign (bytes, Storage.view view ~elements:(Constant (Bytes text)) ~length));
      build field (Copy bytes)
  | _ -> bug "a string literal of type %s" (Ground.to_string ty)

let static_constant st path : Lowered.place =
  match Interface.Definition.constant_type st.context.lookups.interface path with
  | Some ty -> { root = Static { key = Constant path; ty = ground st ty }; projections = [] }
  | None -> bug "no type for the constant %s" (Path.show path)

let list_parts monomorphic ty =
  match Monomorphic.shape monomorphic ty with
  | Record [ (field, Typed storage) ] -> (
      match Storage.elements_of storage with
      | Some element -> (field, storage, element)
      | None -> bug "%s is not a list" (Ground.to_string ty))
  | _ -> bug "%s is not a list" (Ground.to_string ty)

let list_of st ty destination ~site fills =
  let field, _, element = list_parts st.context.monomorphic ty in
  let storage_place = destination / Field field in
  let lower operation arguments destination =
    ignore
      (Intrinsics.lower ~checks:st.context.checks st.context.env st.builder st.context.types
         operation ~type_arguments:[ element ] arguments ~destination ~site)
  in
  lower Storage_with_capacity [ Value (constant_uint64 (List.length fills)) ] (Some storage_place);
  List.iter
    (fun fill ->
      let value = temporary st element in
      fill value;
      lower Storage_push [ Place storage_place; Value (owned st value element) ] None)
    fills

let template_value st template_ty literals ~site ~parts =
  let field_type ty name =
    match Monomorphic.shape st.context.monomorphic ty with
    | Record fields -> (
        match List.assoc_opt name fields with
        | Some (Memory_layout.Typed ty) -> ty
        | _ -> bug "%s has no field %s" (Ground.to_string ty) name)
    | _ -> bug "%s is not a record" (Ground.to_string ty)
  in
  let element list_ty =
    let _, _, element = list_parts st.context.monomorphic list_ty in
    element
  in
  let literals_ty = field_type template_ty "literals" in
  let parts_ty = field_type template_ty "parts" in
  let literal_ty = element literals_ty in
  let slice_ty = field_type literal_ty "text" in
  let built = temporary st template_ty in
  list_of st literals_ty (built / Field "literals") ~site
    (List.map
       (fun text value ->
         let slice = temporary st slice_ty in
         string_literal st slice_ty text ~destination:slice;
         emit st.builder
           (Assign
              (value, Build { ty = literal_ty; variant = None; fields = [ ("text", Copy slice) ] })))
       literals);
  list_of st parts_ty (built / Field "parts") ~site parts;
  built

let pull_loop st ~(option : Ground.ty) ~(call_next : Lowered.place -> unit)
    ~(body : Lowered.place -> unit) =
  in_scope st (fun () ->
      let next = held st (Value option) in
      let depth = List.length st.scopes in
      let test = block st.builder and inside = block st.builder and after = block st.builder in
      finish st.builder (Goto test);
      start st.builder test;
      call_next next;
      let more = local st.builder (Raw Bool) in
      emit st.builder (Assign (at more, Is_variant (next, "Some")));
      branch st.builder (Copy (at more)) ~yes:inside ~no:after;
      start st.builder inside;
      in_scope st (fun () ->
          looping st ~continue_:test ~break_:after ~depth (fun () ->
              body (next / Variant_field { variant = "Some"; field = "value" })));
      finish st.builder (Goto test);
      start st.builder after)
