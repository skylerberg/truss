(* Calls and the evidence they need: a trait method's implementation, how each
   argument is passed, capabilities' and [any] values' tables, and calling
   an instance; with literals and the standard types lowering builds. *)

open Definitions
open Lowering
open Lir_builder

(* The [impl] that evidence stands for in this instance, with the type
   arguments for the [impl]'s generic parameters. *)
let resolve_impl st ~(trait : Types.trait_reference) ~self_type ~(evidence : Core.evidence) =
  let substitute = Types.substitute st.frame.code.substitution in
  let impl, arguments =
    match evidence with
    | Impl { impl; arguments } ->
        ( impl,
          List.map
            (fun (parameter, argument) ->
              (parameter, Types.substitute_argument st.frame.code.substitution argument))
            arguments )
    | Bound -> (
        let self = st.context.monomorphic.normalize (substitute self_type) in
        match
          Interface.Impls.implements st.context.database
            ~bounds:(fun _ -> [])
            self
            (let trait = Types.substitute_trait st.frame.code.substitution trait in
             {
               trait with
               trait_arguments =
                 List.map
                   (function
                     | Types.Type ty -> Types.Type (st.context.monomorphic.normalize ty)
                     | argument -> argument)
                   trait.trait_arguments;
             })
        with
        | Some (From_impl { impl; substitution }) -> (impl, substitution)
        | _ -> bug "no impl of %s for %s" (Types.show_trait trait) (Types.show self))
    | Dynamic -> bug "a call through any, which reaches no one instance"
  in
  let impl_interface =
    match Interface.Impls.impl_interface st.context.database impl with
    | Some position -> position
    | None -> bug "no interface for %s" (Path.show impl)
  in
  let impl_arguments =
    List.map
      (fun (generic : Types.generic) ->
        match List.assoc_opt generic.generic arguments with
        | Some argument -> Monomorphic.ground_argument st.context.monomorphic [] argument
        | None -> bug "the impl's parameter %s is not bound" generic.generic.name)
      impl_interface.impl_generics
  in
  (impl, impl_arguments)

(* The instance a trait method's call reaches, once the types are known. *)
let trait_method_key st ~(trait : Types.trait_reference) ~name ~receiver ~self_type ~type_arguments
    ~(evidence : Core.evidence) =
  let impl, impl_arguments = resolve_impl st ~trait ~self_type ~evidence in
  Instance.Code
    {
      path = Method { owner = impl; name; receiver };
      type_arguments =
        impl_arguments
        @ List.map
            (Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution)
            type_arguments;
    }

(* An argument as it is passed: by value, by address, or as an owned
   value. *)
(* The operand that gives a place to a parameter that takes it as
   [lir_ty]. *)
let operand_as st (mode : Types.mode) ty (place : Lir.place) (lir_ty : Lir.ty option) =
  match lir_ty with
  | None -> None
  | Some (Pointer _) when mode = Types.Own -> Some (Lir.Moved_address place)
  | Some (Pointer { writable; _ }) -> Some (Lir.Address { place; writable })
  | Some _ -> ( match mode with Own -> Some (owned st place ty) | Read | Mut -> Some (Copy place))

let pass st (mode : Types.mode) ty place =
  operand_as st mode ty place (Convention.parameter st.context.env (Monomorphic.mode mode) ty)

let hold st mode ty place =
  operand_as st mode ty place (Convention.held st.context.env (Monomorphic.mode mode) ty)

(* Calls a function instance with arguments that are places of their
   parameter types, writing the result to [destination]. *)
(* A capability's method: its slot in every table of the capability, and
   its signature. *)
(* A method's slot in a table whose first method is at [first], and its
   signature. *)
let method_slot ~first ~missing (methods : Types.trait_method list) name =
  match
    List.find_index
      (fun (trait_method : Types.trait_method) -> trait_method.method_name = name)
      methods
  with
  | Some index -> (first + index, (List.nth methods index).method_signature)
  | None -> missing ()

let capability_method context capability name =
  let interface =
    match demand context Environment.trait_interface capability with
    | Some position -> position
    | None -> bug "no interface for %s" (Path.show capability)
  in
  method_slot ~first:0 interface.methods name ~missing:(fun () ->
      bug "%s has no method %s" (Path.show capability) name)

(* The C signature of an entry in a capability's table, which every caller
   and every entry agree on: the evidence, then the method's own. *)
let entry_signature context (signature : Types.signature) =
  let lir, result =
    lir_signature context []
      ~parameters:(interface_parameters { signature with receiver = None })
      ~has_defaults:false signature.output
  in
  ({ lir with parameters = Convention.evidence :: lir.parameters }, result)

(* Whether a trait's method has an entry in an [any] table: the checker
   lets a call through [any] reach it, and it returns a value. *)
let callable_through_any trait (trait_method : Types.trait_method) =
  trait_method.method_receiver <> Static
  && Interface.Impls.through_any ~trait trait_method = Callable
  && match trait_method.method_signature.output with Returns _ -> true | _ -> false

(* The methods of a trait an [any] table has an entry for, in order. *)
let any_methods context trait =
  match demand context Environment.trait_interface trait with
  | Some position -> List.filter (callable_through_any trait) position.methods
  | None -> bug "no interface for %s" (Path.show trait)

(* A method's slot in an [any] table, after the drop in slot 0. *)
let dynamic_slot context trait name =
  method_slot ~first:1 (any_methods context trait) name ~missing:(fun () ->
      bug "%s cannot be called through any" name)

(* The instantiation of a trait's [Self] and parameters in a method called
   through an [any] type: [Self] is the [any] type, which fixes each
   associated type. *)
let any_substitution context ~(any : Types.trait_reference) trait : Types.substitution =
  match demand context Environment.trait_interface trait with
  | Some interface ->
      let reference =
        if Path.equal trait any.trait then any
        else
          match
            List.find_opt
              (fun (bound : Types.trait_reference) -> Path.equal bound.trait trait)
              (Interface.Properties.bound_closure context.database ~self:(Types.Any any) any)
          with
          | Some bound -> bound
          | None -> bug "%s is not a trait of %s" (Path.show trait) (Types.show (Types.Any any))
      in
      Interface.Properties.trait_substitution interface ~self:(Types.Any any) reference
  | None -> bug "no interface for %s" (Path.show trait)

(* An entry in an [any] table: its C signature, which is the value's
   pointer, then the method's own, with the evidence for its capabilities; how
   its result is passed; and the capabilities that the evidence is for. The
   method is [trait]'s, read for the [any] type. An associated capability
   set of an [any] type is empty, so a method that uses [Self.Uses] takes
   no evidence for it: the caller cannot name the capabilities of the type
   that the value hides, and the checker converts a value to [any] only
   where each set of its type is empty. *)
let any_entry_signature context ~any ~trait (signature : Types.signature) =
  let substitution = any_substitution context ~any trait in
  let lir, result =
    lir_signature context substitution
      ~parameters:(interface_parameters { signature with receiver = None })
      ~has_defaults:false ~uses:signature.uses signature.output
  in
  ( { lir with parameters = Lir.Raw (Pointer Opaque) :: lir.parameters },
    result,
    evidence_for context substitution signature.uses )

(* Evidence on the stack that a capability is implemented by the value
   [implementation] points at: its [impl]'s table, and the evidence the
   [impl] uses, which the code here has. *)
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
  Lir.Address { place = at slot; writable = false }

(* The evidence for a capability, where the code being lowered has it. In a
   method of an [impl] of the capability that does not use it, a function
   value that uses it means the implementation itself, so the evidence is
   the implementation's own: its [self]. *)
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
            | _ when Memory_layout.has_zero_size st.context.env self_ty -> Lir.Constant Null
            | Some self -> Lir.Address { place = self; writable = true }
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

(* The capabilities whose evidence the [next] of a cursor over the method
   takes: the method's own. A cursor holds no evidence. The evidence it
   was made with is in the frame of a [provide], and a cursor that held it
   and outlived that frame would use the implementation after it was
   dropped. *)
let cursor_evidence context (yielding : Ground.yielding) =
  let code = code_of context yielding.method_ yielding.type_arguments in
  evidence_for context code.substitution code.uses

(* Writes a cursor over a yielding method to [destination]. The cursor holds
   the call's arguments, in the order of the pulled method's parameters:
   its own, then the mask of defaults passed. *)
let cursor_into st ~path ~type_arguments ~(signature : Types.signature)
    ~(arguments : (Types.mode * Ground.ty * Lir.place) list) ~mask destination =
  let held = List.filter_map (fun (mode, ty, place) -> hold st mode ty place) arguments in
  let mask = if has_defaults signature then [ constant_int UInt64 (Z.of_int mask) ] else [] in
  let fields =
    List.mapi (fun position operand -> (Convention.cursor_parameter position, operand)) (held @ mask)
  in
  emit st.builder
    (Assign
       ( destination,
         Build
           {
             ty = Cursor { method_ = path; type_arguments };
             variant = None;
             fields = (Convention.cursor_state, Constant (Integer (UInt32, Z.zero))) :: fields;
           } ))

(* Writes a lambda's function value to [destination], and lowers the lambda
   as a nested function of the instance. The enclosing function fills an
   environment with a pointer to each captured variable, given as its key,
   its place, and its type. In the lambda's own state, [bind_capture] binds
   each captured variable to the place the environment gives it, and [body]
   lowers the body, given the place, the mode, and the type of each
   parameter. The lambda is given its environment, then its type's
   parameters, then the evidence for its type's capabilities, which its
   caller passes: that is the only evidence its code can reach. [output] is
   the lambda's result, which a [?] in it returns early. *)
let nested_function st ~(function_type : Ground.function_type) ~(output : Types.result option)
    ~(captures : (Lir.place * Ground.ty) list)
    ~(body : state -> captures:Lir.place list -> (Lir.place * Ground.mode * Ground.ty) list -> unit)
    destination =
  let index = List.length !(st.nested) in
  st.nested := !(st.nested) @ [ None ];
  let captured =
    List.mapi
      (fun position (place, ty) -> (Printf.sprintf "capture%d" position, place, ty))
      captures
  in
  let environment =
    List.map
      (fun (name, _, ty) -> (name, Lir.Pointer { target = Value ty; writable = false }))
      captured
  in
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
    enter st.context ~form:Ordinary ~nested:st.nested
      {
        st.frame with
        on_yield = None;
        yield_into = None;
        lent_into = None;
        exit = None;
        code =
          (match output with
          | Some output -> { st.frame.code with result = output }
          | None -> st.frame.code);
      }
  in
  let builder = inner.builder in
  let environment_parameter = local builder ~name:"environment" (Raw (Nullable_pointer Opaque)) in
  let result_ty =
    match function_type.result with Returns ty -> ty | _ -> bug "a lambda that yields"
  in
  result_slot inner (Convention.result st.context.env result_ty);
  let parameter_places =
    List.map
      (fun ((mode : Ground.mode), ty) -> (parameter inner ~owned:(mode = Own) mode ty, mode, ty))
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
           { Lir.root = Local environment_pointer; projections = [ Deref; Field name; Deref ] })
         captured)
    (List.map (fun ((_, place), mode, ty) -> (place, mode, ty)) parameter_places);
  let function_ =
    finish_function inner ~first:[ environment_parameter ]
      ~rest:(List.filter_map (fun ((arrives, _), _, _) -> arrives) parameter_places @ evidence)
      ()
  in
  st.nested :=
    List.mapi
      (fun position nested_function ->
        if position = index then Some { function_ with environment } else nested_function)
      !(st.nested)

(* Calls a function value with arguments that are already in places, one for
   each parameter of its type, and the evidence for its type's capabilities. *)
let call_indirect st ~(function_type : Ground.function_type) ~(value : Lir.place)
    (places : Lir.place list) destination =
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
    Lir.Indirect
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
  | Yields _ | Lends _ -> bug "a function value that yields"

(* Calls a method through an [any] value: the entry in its table, given the
   value's pointer, then the arguments, then the evidence the method uses. *)
let call_through_any st ~(any_type : Types.trait_reference) ~trait ~name ~(any : Lir.place)
    ~(arguments : (Types.mode * Ground.ty * Lir.place) list) destination =
  let slot, signature = dynamic_slot st.context trait name in
  let lir_signature, result, capabilities =
    any_entry_signature st.context ~any:any_type ~trait signature
  in
  let passed = List.filter_map (fun (mode, ty, place) -> pass st mode ty place) arguments in
  let evidence = List.map (evidence_of st) capabilities in
  let target =
    Lir.Table_call
      {
        table = Copy (any / Field "vtable");
        value = Copy (any / Field "value");
        slot;
        signature = lir_signature;
      }
  in
  emit st.builder
    (Call
       { target; arguments = passed @ evidence; result = Convention.destination result destination });
  if not lir_signature.returns then unreachable_block st

(* Runs [f] with the current frame set to the definition of a named type,
   with the type's generic parameters bound to the type's arguments. A
   field's default is lowered there, because it is written in the type's
   definition. *)
let in_type_definition st (ty : Ground.ty) nested_function =
  let path, arguments =
    match ty with
    | Named { path; arguments } -> (path, arguments)
    | _ -> bug "defaults of %s" (Ground.to_string ty)
  in
  let key = key_of st.context path in
  let interface =
    match demand st.context Environment.type_interface path with
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

(* Writes the debug text of the value at a place to the test's echo
   output, with the position it was echoed at. *)
let echo st place ty ~site =
  let output = temporary st Glue.output_ty in
  emit st.builder (Assign (output, Storage.empty Glue.output_ty));
  let arguments = if is_zero_size st ty then [] else [ Lir.Address { place; writable = false } ] in
  emit st.builder
    (Call
       {
         target =
           Direct
             {
               function_ = Instance (Debug ty);
               signature = Glue.debug_signature st.context.glue ty;
             };
         arguments = arguments @ [ Address { place = output; writable = true } ];
         result = Discarded;
       });
  emit st.builder
    (Echo { text = Copy (Storage.buffer output); length = Copy (Storage.length output); site })

(* Writes an [any] value to [destination]: the value at [value], moved into
   a heap block of its own, with the method table of its type's [impl]. *)
let any_into st ~any_ty ~inner_ty ~impl ~type_arguments ~(value : Lir.place) destination =
  let block = local st.builder (Raw (Pointer Opaque)) in
  if is_zero_size st inner_ty then emit st.builder (Assign (at block, Use (Constant (Bytes ""))))
  else begin
    emit st.builder
      (Call
         {
           target = Intrinsic Allocate;
           arguments = [ Constant (Size_of inner_ty); Constant (Alignment_of inner_ty) ];
           result = Returned (at block);
         });
    (* The pointer is [borrowed] so that drop elaboration does not track
       the block's contents, which the [any] value owns. *)
    let typed =
      local st.builder ~borrowed:true (Pointer { target = Value inner_ty; writable = true })
    in
    emit st.builder (Assign (at typed, Use (Copy (at block))));
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
                 ("value", Copy (at block));
                 ("vtable", Constant (Symbol_address (Any_table { impl; type_arguments })));
               ];
           } ))

(* The evidence that a [provide] adds for one implementation: for each
   capability its type provides, the [impl]'s table with a pointer to the
   implementation. *)
let provided_evidence st ~(implementation : Lir.operand) provides =
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

(* The instance that a method's key is called as. The [next] of a cursor
   over a yielding function is the function's state machine. *)
let called (key : Instance.key) : Instance.key =
  match key with
  | Code { path = Method { owner; name = "next"; _ }; type_arguments } -> (
      match Interface.Impls.cursor_of_impl owner with
      | Some method_ -> Cursor_next { method_; type_arguments }
      | None -> key)
  | key -> key

(* The mask of a call that passes every argument: a bit for each parameter
   that has a default. *)
let all_passed (signature : Types.signature) =
  let defaulted =
    List.length
      (List.filter
         (fun (parameter : Types.parameter_info) -> parameter.has_default)
         signature.parameters)
  in
  (1 lsl defaulted) - 1

(* Calls an instance with an argument in a place for each parameter. [mask]
   says which of the parameters with defaults were passed, where the call
   left some to the callee; without it every argument is one to use. *)
(* The signature of a call of a function instance with arguments that are
   places of their parameter types, its result, and the operands it passes:
   each argument, then the mask of defaults passed, then the evidence. *)
let instance_call st ~(signature : Types.signature) ~substitution
    ~(arguments : (Types.mode * Ground.ty * Lir.place) list) ?mask () =
  let mask = match mask with Some mask -> mask | None -> all_passed signature in
  let lir_signature, result =
    lir_signature st.context substitution ~parameters:(interface_parameters signature)
      ~has_defaults:(has_defaults signature) ~uses:signature.uses signature.output
  in
  let passed = List.filter_map (fun (mode, ty, place) -> pass st mode ty place) arguments in
  let mask =
    (if has_defaults signature then [ constant_int UInt64 (Z.of_int mask) ] else [])
    @ List.map (evidence_of st) (evidence_for st.context substitution signature.uses)
  in
  (lir_signature, result, passed @ mask)

let call_instance st key ~(signature : Types.signature) ~substitution
    ~(arguments : (Types.mode * Ground.ty * Lir.place) list) ?mask ~destination () =
  let lir_signature, result, operands =
    instance_call st ~signature ~substitution ~arguments ?mask ()
  in
  let target = Lir.Direct { function_ = Instance (called key); signature = lir_signature } in
  emit st.builder
    (Call { target; arguments = operands; result = Convention.destination result destination });
  if not lir_signature.returns then unreachable_block st

(* A number literal's value. *)
type literal = Integer_value of Z.t | Float_value of float

let constant_of st ty (literal : literal) : Lir.operand =
  match (literal, scalar_of st ty) with
  | Integer_value value, Integer integer -> constant_int integer value
  | Integer_value value, Character -> Constant (Character (Z.to_int value))
  | Float_value value, Float64 -> Constant (Float64 (Int64.bits_of_float value))
  | Float_value value, Float32 -> Constant (Float32 (Int32.bits_of_float value))
  | _ -> bug "a literal of type %s" (Ground.to_string ty)

(* Writes a string literal to [destination]. Its bytes are static data: a
   [String] holds them as storage with capacity 0, and a [StringSlice] views
   them. *)
let string_literal st (ty : Ground.ty) text ~(destination : Lir.place) =
  let length = usize (String.length text) in
  let build field operand =
    emit st.builder
      (Assign (destination, Build { ty; variant = None; fields = [ (field, operand) ] }))
  in
  match (ty, Monomorphic.shape st.context.monomorphic ty) with
  | Named { path; _ }, Record [ (field, Typed storage) ] when Well_known.is String path ->
      let bytes = temporary st storage in
      emit st.builder
        (Assign (bytes, Storage.static storage ~elements:(Constant (Bytes text)) ~length));
      build field (Move bytes)
  | _, Record [ (field, Typed view) ] ->
      let bytes = temporary st view in
      emit st.builder (Assign (bytes, Storage.view view ~elements:(Constant (Bytes text)) ~length));
      build field (Copy bytes)
  | _ -> bug "a string literal of type %s" (Ground.to_string ty)

(* A constant's static data, as a place. *)
let static_constant st path : Lir.place =
  match demand st.context Environment.constant_type path with
  | Some ty -> { root = Static { key = Constant path; ty = ground st ty }; projections = [] }
  | None -> bug "no type for the constant %s" (Path.show path)

let list_parts monomorphic ty =
  match Monomorphic.shape monomorphic ty with
  | Record [ (field, Typed storage) ] -> (
      match Monomorphic.representation monomorphic storage with
      | Storage element -> (field, storage, element)
      | _ -> bug "%s is not a list" (Ground.to_string ty))
  | _ -> bug "%s is not a list" (Ground.to_string ty)

(* Writes a [List] to [destination], with storage of exactly its length. Each
   fill writes one element to the place it is given. *)
let list_of st ty destination ~site fills =
  let field, _, element = list_parts st.context.monomorphic ty in
  let storage_place = destination / Field field in
  let lower operation arguments destination =
    ignore
      (Intrinsics.lower ~checks:st.context.checks st.context.env st.builder st.context.types
         operation ~type_arguments:[ element ] arguments ~destination ~site)
  in
  lower Storage_with_capacity [ Value (usize (List.length fills)) ] (Some storage_place);
  List.iter
    (fun fill ->
      let value = temporary st element in
      fill value;
      lower Storage_push [ Place storage_place; Value (owned st value element) ] None)
    fills

(* A [Template] of these literal texts, each a [Literal] of static bytes,
   with one part for each fill in [parts]. *)
let template_value st template_ty texts ~site ~parts =
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
       texts);
  list_of st parts_ty (built / Field "parts") ~site parts;
  built

(* The type that a lending or yielding method gives at its [yield], for the
   method's type arguments. *)
let yielded_type st path type_arguments =
  let signature = signature_of st.context path in
  match signature.output with
  | Yields (_, ty) | Lends (_, ty) ->
      Monomorphic.ground st.context.monomorphic (bind signature.generics type_arguments) ty
  | Returns _ -> bug "%s does not yield" (Path.show path)

(* A yielding method's yield type, in an instance. *)
let cursor_element context (yielding : Ground.yielding) =
  let signature = signature_of context yielding.method_ in
  match signature.output with
  | Yields (_, ty) ->
      Monomorphic.ground context.monomorphic (bind signature.generics yielding.type_arguments) ty
  | _ -> bug "%s does not yield" (Path.show yielding.method_)

(* A cursor's [next] result type: an [Option] of its yield type. *)
let cursor_result context yielding : Ground.ty =
  Named { path = Well_known.path Option; arguments = [ Type (cursor_element context yielding) ] }

(* Calls [next] on a cursor: the pulled method's state machine, which takes
   the method's evidence from this call. *)
let call_next st (yielding : Ground.yielding) cursor destination =
  let option = cursor_result st.context yielding in
  let cursor_pointer = Lir.Pointer { target = Value (Cursor yielding); writable = true } in
  let target signature = Lir.Direct { function_ = Instance (Cursor_next yielding); signature } in
  let self = Lir.Address { place = cursor; writable = true } in
  let evidence = List.map (evidence_of st) (cursor_evidence st.context yielding) in
  let convention = Convention.result st.context.env option in
  emit st.builder
    (Call
       {
         target =
           target
             (Convention.signature
                (cursor_pointer :: List.map (fun _ -> Convention.evidence) evidence)
                convention);
         arguments = self :: evidence;
         result = Convention.destination convention destination;
       })

(* Pulls a cursor until it ends, running [body] with the place of each
   value. [call_next] calls the cursor's [next], which writes an [Option] of
   type [option] to the place it is given. The loop owns the value that
   [next] gave, so whatever the body did not take is dropped before the
   next value is asked for, and on every way out. *)
let pull_loop st ~(option : Ground.ty) ~(call_next : Lir.place -> unit) ~(body : Lir.place -> unit)
    =
  in_scope st (fun () ->
      let next = binding st option in
      let depth = List.length st.scopes in
      let test = block st.builder and inside = block st.builder and after = block st.builder in
      finish st.builder (Goto test);
      start st.builder test;
      if not (trivial st option) then emit st.builder (Drop next);
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

(* A heap block for a cursor, which the current scope frees. A loop over a
   recursive yielding method keeps its cursor there, so that a cursor over
   the method can hold another. *)
let boxed_cursor st (yielding : Ground.yielding) : Lir.place =
  let cursor_ty = Ground.Cursor yielding in
  let boxed =
    local st.builder ~name:"cursor" (Pointer { target = Value cursor_ty; writable = true })
  in
  emit st.builder
    (Call
       {
         target = Intrinsic Allocate;
         arguments = [ Constant (Size_of cursor_ty); Constant (Alignment_of cursor_ty) ];
         result = Returned (at boxed);
       });
  free_in_scope st (at boxed);
  { root = Local boxed; projections = [ Deref ] }
