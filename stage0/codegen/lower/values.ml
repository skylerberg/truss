(* Values: literals, templates, collections, [provide], [?], lambdas,
   [with], interpolation, [any], and [echo]. *)

open Definitions
open Lowering
open Targets
open Matching
open Calls
open Lir_builder

let block_into st = !Forward.block_into st
let expression st = !Forward.expression st
let into st = !Forward.into st
let operand st = !Forward.operand st
let place_expression st = !Forward.place_expression st
let statement st = !Forward.statement st

(* A literal negated directly, which the type checker checked as one
   literal. *)
let rec negated_literal st ty (inner : S.expression) =
  match literal st inner.id with
  | Integer_value value -> constant_of st ty (Integer_value (Z.neg value))
  | Float_value value -> constant_of st ty (Float_value (Float.neg value))

(* A [[...]] literal: an [Array], filled in place, or a [List], with storage
   of exactly its length, in one allocation. *)
and list_into st (ty : Ground.ty) (elements : S.expression list) destination ~span =
  match ty with
  | Named
      { path = Top { module_ = { package = "standard"; modules = [ "set" ] }; name = "Set" }; _ } ->
      collection_into st ty destination ~span
        (List.map (fun (e : S.expression) -> [ (e, type_of st e.id) ]) elements)
  | _ -> (
      match Monomorphic.shape st.context.monomorphic ty with
      | Array _ ->
          List.iteri
            (fun i (e : S.expression) -> into st e (destination / Index (usize i)))
            elements
      | Record [ (_, Typed _) ] ->
          list_of st ty destination ~span
            (List.map (fun (e : S.expression) value -> into st e value) elements)
      | _ -> unsupported st span "a list literal of %s" (Ground.to_string ty))

(* A [List] in [destination], with storage of exactly its length, holding
   what each fill writes to the element's place it is given. *)
and list_of st ty destination ~span fills =
  match Monomorphic.shape st.context.monomorphic ty with
  | Record [ (field, Typed storage) ] -> (
      match Monomorphic.kind st.context.monomorphic storage with
      | Storage element ->
          let storage_place = destination / Field field in
          let lower operation arguments destination =
            ignore
              (Intrinsics.lower ~checks:st.context.checks st.context.env st.b st.context.types
                 operation ~type_arguments:[ element ] arguments ~destination ~site:(site st span))
          in
          lower Storage_with_capacity [ Value (usize (List.length fills)) ] (Some storage_place);
          List.iter
            (fun fill ->
              let value = temporary st element in
              fill value;
              lower Storage_push [ Place storage_place; Value (owned st value element) ] None)
            fills
      | _ -> bug "a list of %s" (Ground.to_string ty))
  | _ -> bug "%s is not a list" (Ground.to_string ty)

(* A tagged string, such as [Sql"..."]: a [Template] of its literal text,
   each piece a [Literal] of static bytes, and its parts, each made the
   tag's [Part] through its [From], given to the tag's [from_template]. *)
and template_into st (literal : S.string_literal) (template : C.template) destination ~span =
  let call_ =
    match template.from_template with Some c -> c | None -> bug "a tag with no from_template"
  in
  let path, type_arguments =
    match resolve_callee st call_ with Some r -> r | None -> bug "a from_template not resolved"
  in
  let signature = signature_of st.context path in
  let substitution = bind signature.generics type_arguments in
  let mode, template_ty =
    match interface_parameters signature with
    | [ (mode, ty) ] -> (mode, Monomorphic.ground st.context.monomorphic substitution ty)
    | _ -> bug "from_template takes one template"
  in
  let texts =
    literal.first.value :: List.map (fun (_, (text : S.text)) -> text.value) literal.rest
  in
  let built =
    template_value st template_ty texts ~span
      ~parts:
        (List.map2
           (fun ((part : S.expression), _) conversion value ->
             match conversion with
             | Some (call_ : C.call) ->
                 call_with st call_ ~expressions:[ part ] ~arguments:call_.arguments value ~span
             | None -> into st part value)
           literal.rest template.part_conversions)
  in
  call_instance st
    (Code { path; type_arguments })
    ~signature ~substitution
    ~arguments:[ (mode, template_ty, built) ]
    ~mask:0 ~destination

(* A [Template] of these literal texts, each piece a [Literal] of static
   bytes, with its parts each filled in by one of [parts]. *)
and template_value st template_ty texts ~span ~parts =
  let field_type ty name =
    match Monomorphic.shape st.context.monomorphic ty with
    | Record fields -> (
        match List.assoc_opt name fields with
        | Some (Memory_layout.Typed ty) -> ty
        | _ -> bug "%s has no field %s" (Ground.to_string ty) name)
    | _ -> bug "%s is not a record" (Ground.to_string ty)
  in
  let element list_ty =
    match Monomorphic.shape st.context.monomorphic list_ty with
    | Record [ (_, Typed storage) ] -> (
        match Monomorphic.kind st.context.monomorphic storage with
        | Storage element -> element
        | _ -> bug "%s is not a list" (Ground.to_string list_ty))
    | _ -> bug "%s is not a list" (Ground.to_string list_ty)
  in
  let literals_ty = field_type template_ty "literals" in
  let parts_ty = field_type template_ty "parts" in
  let literal_ty = element literals_ty in
  let slice_ty = field_type literal_ty "text" in
  let built = temporary st template_ty in
  list_of st literals_ty (built / Field "literals") ~span
    (List.map
       (fun text value ->
         let slice = string_place st slice_ty text in
         emit st.b
           (Assign
              (value, Build { ty = literal_ty; variant = None; fields = [ ("text", Copy slice) ] })))
       texts);
  list_of st parts_ty (built / Field "parts") ~span parts;
  built

(* A [Set] or [Map] literal: the collection made empty, then each item
   inserted with the type's own [insert], which keeps it in order and keeps
   the last of equal keys. Each item is the arguments [insert] takes after
   the collection. *)
and collection_into st ty destination ~span items =
  let path, arguments =
    match ty with
    | Named { path; arguments } -> (path, arguments)
    | _ -> bug "a collection literal of %s" (Ground.to_string ty)
  in
  (match Monomorphic.shape st.context.monomorphic ty with
  | Record [ (field, Typed list) ] -> list_into st list [] (destination / Field field) ~span
  | _ -> bug "%s is not a record of a list" (Ground.to_string ty));
  let insert = Path.Method { owner = path; name = "insert"; receiver = Mut } in
  let signature = signature_of st.context insert in
  let substitution = bind signature.generics arguments in
  List.iter
    (fun parts ->
      let values =
        List.map
          (fun ((e : S.expression), part_ty) ->
            let value = temporary st part_ty in
            into st e value;
            (T.Own, part_ty, value))
          parts
      in
      call_instance st
        (Code { path = insert; type_arguments = arguments })
        ~signature ~substitution
        ~arguments:((T.Mut, ty, destination) :: values)
        ~mask:0
        ~destination:(temporary st (Monomorphic.builtin Unit)))
    items

(* [provide]: each implementation evaluated once, as a place or a temporary
   that lives to the end of the statement, and for each capability it
   provides, evidence on the stack pointing at it, its table, and the
   evidence it captures from the code around the [provide]. The body runs
   with that evidence. *)
and provide st (e : S.expression) implementations body destination =
  let provides =
    match st.frame.code.checked.provides.(e.id) with
    | Some p -> p.implementations
    | None -> bug "a provide with no meaning"
  in
  let around = st.evidence in
  let rec provided_by (e : S.expression) =
    match List.assoc_opt e.id provides with
    | Some provided -> provided
    | None -> (
        match e.kind with
        | Mode (_, inner) | Parenthesized inner -> provided_by inner
        | _ -> bug "an implementation with no capabilities")
  in
  let added =
    List.concat_map
      (fun (implementation : S.expression) ->
        let ty = type_of st implementation.id in
        let pointer =
          if zero_size st ty then Lir.Constant Null
          else Address { place = expression st implementation; writable = true }
        in
        List.map
          (fun (provided : C.provided) ->
            let interface = impl_interface st.context provided.impl in
            let type_arguments =
              List.map
                (fun (g : T.generic) ->
                  match List.assoc_opt g.generic provided.arguments with
                  | Some a ->
                      Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution
                        a
                  | None -> bug "an unbound parameter of %s" (Path.show provided.impl))
                interface.impl_generics
            in
            let outer =
              List.map
                (fun capability ->
                  match List.find_opt (fun (path, _) -> Path.equal path capability) around with
                  | Some (_, operand) -> operand
                  | None -> bug "no evidence for %s here" (Path.show capability))
                (evidence_for [] interface.impl_uses)
            in
            let slot = local st.b (Evidence (List.length outer)) in
            emit st.b
              (Call
                 {
                   target = Intrinsic Evidence_fill;
                   arguments =
                     Address { place = at slot; writable = true }
                     :: pointer
                     :: Constant (Symbol_address (Table { impl = provided.impl; type_arguments }))
                     :: outer;
                   result = Discarded;
                 });
            (provided.capability, Lir.Address { place = at slot; writable = false }))
          (provided_by implementation))
      implementations
  in
  st.evidence <- added @ around;
  block_into st body (Some destination);
  st.evidence <- around

(* [?]: the error, or [None], returned at once, as the function's own
   result type; otherwise the value inside. *)
and try_ st (inner : S.expression) destination =
  let ty = type_of st inner.id in
  let value = expression st inner in
  let variants =
    match Monomorphic.shape st.context.monomorphic ty with
    | Sum v -> v
    | _ -> bug "? on %s" (Ground.to_string ty)
  in
  let success, failure =
    match List.map (fun (v : Memory_layout.variant_shape) -> v.name) variants with
    | [ "Ok"; "Err" ] -> ("Ok", "Err")
    | [ "Some"; "None" ] -> ("Some", "None")
    | _ -> bug "? on %s" (Ground.to_string ty)
  in
  let fields name =
    (List.find (fun (v : Memory_layout.variant_shape) -> v.name = name) variants).fields
  in
  let failed = local st.b (Raw Bool) in
  emit st.b (Assign (at failed, Is_variant (value, failure)));
  let leave = block st.b and stay = block st.b in
  finish st.b (Switch { value = Copy (at failed); cases = [ (Z.one, leave) ]; default = Some stay });
  start st.b leave;
  let result_ty =
    match st.frame.code.result with
    | Returns t -> ground st t
    | _ -> bug "? in a method that yields"
  in
  let returned =
    List.map
      (fun (name, member) ->
        match member with
        | Memory_layout.Typed field_ty ->
            (name, owned st (value / Variant_field { variant = failure; field = name }) field_ty)
        | Raw _ -> bug "a raw field")
      (fields failure)
  in
  let built = temporary st result_ty in
  emit st.b (Assign (built, Build { ty = result_ty; variant = Some failure; fields = returned }));
  clear_result st;
  Option.iter (fun result -> emit st.b (Assign (result, Use (Move built)))) (result_place st);
  leave_to st 0;
  finish st.b (return_result st);
  start st.b stay;
  match fields success with
  | [ (name, Typed field_ty) ] ->
      emit st.b
        (Assign
           ( destination,
             Use (owned st (value / Variant_field { variant = success; field = name }) field_ty) ))
  | _ -> bug "? on a variant with more than one field"

(* A lambda: a nested function whose environment holds the address of each
   local it reads, made on the caller's stack, so making one never
   allocates. *)
and lambda st (e : S.expression) ~(parameters : S.pattern list) ~(body : S.block) destination =
  if st.pulling then unsupported st e.span "a lambda in a yielding method that is pulled";
  let f =
    match type_of st e.id with Function f -> f | ty -> bug "a lambda of %s" (Ground.to_string ty)
  in
  let captures = Option.value st.frame.code.checked.captures.(e.id) ~default:[] in
  let index = List.length !(st.nested) in
  st.nested := !(st.nested) @ [ None ];
  let captured =
    List.mapi
      (fun i local ->
        let place =
          match Hashtbl.find_opt st.frame.bindings local with
          | Some p -> p
          | None -> bug "an unbound capture"
        in
        let ty =
          match st.frame.code.checked.local_types.(local) with
          | Some ty -> ground st ty
          | None -> bug "a capture with no type"
        in
        (Printf.sprintf "capture%d" i, local, place, ty))
      captures
  in
  let environment =
    List.map
      (fun (name, _, _, ty) -> (name, Lir.Pointer { target = Value ty; writable = false }))
      captured
  in
  (* The caller fills in the environment and makes the value. *)
  let environment_local = at (local st.b (Environment index)) in
  List.iter
    (fun (name, _, place, _) ->
      emit st.b (Assign (environment_local / Field name, Use (Address { place; writable = false }))))
    captured;
  emit st.b
    (Assign
       ( destination,
         Function_value
           {
             code = Nested index;
             environment = Some (Address { place = environment_local; writable = false });
           } ));
  (* The lambda itself: it is given its environment, then what its type
     takes, then the evidence for what its type uses, passed by whoever
     calls it, which is the only evidence its code can reach. *)
  let inner =
    enter st.context ~pulling:st.pulling ~nested:st.nested
      {
        st.frame with
        bindings = Hashtbl.copy st.frame.bindings;
        on_yield = None;
        exit = None;
        (* What the lambda returns, which a [?] in it returns early. *)
        code =
          (match raw_type_of st e.id with
          | Some (T.Function f) -> { st.frame.code with result = f.output }
          | _ -> st.frame.code);
      }
  in
  let b = inner.b in
  let environment_parameter = local b ~name:"environment" (Raw (Nullable_pointer Opaque)) in
  let result_ty = match f.result with Returns ty -> ty | _ -> bug "a lambda that yields" in
  result_slot inner (Convention.result st.context.env result_ty);
  let taken =
    List.map
      (fun ((mode : Ground.mode), ty) -> (parameter inner ~owned:(mode = Own) mode ty, mode, ty))
      f.parameters
  in
  let evidence = evidence_parameters inner f.uses in
  let environment_pointer = local b (Pointer { target = Environment index; writable = false }) in
  start b (block b);
  emit b (Assign (at environment_pointer, Use (Copy (at environment_parameter))));
  List.iter
    (fun (name, local, _, _) ->
      Hashtbl.replace inner.frame.bindings local
        { Lir.root = Local environment_pointer; projections = [ Deref; Field name; Deref ] })
    captured;
  List.iter2
    (fun (pattern : S.pattern) ((_, place), (mode : Ground.mode), ty) ->
      bind_pattern inner pattern place ty ~owned:(mode = Own))
    parameters taken;
  block_into inner body (result_place inner);
  let function_ =
    finish_function inner ~first:[ environment_parameter ]
      ~rest:(List.filter_map (fun ((arrives, _), _, _) -> arrives) taken @ evidence)
      ()
  in
  st.nested :=
    List.mapi (fun i f -> if i = index then Some { function_ with environment } else f) !(st.nested)

(* [base with (field: value)]: the base as an owned value, then each field
   written in place, which costs one write per field. *)
and with_ st (base : S.expression) (updates : S.update list) destination =
  let ty = type_of st base.id in
  (match place_expression st base with
  | Some place -> take st place ty ~destination
  | None -> into st base destination);
  List.iter
    (fun (update : S.update) ->
      match update.kind with
      | Update { field; path; value } -> (
          let target =
            List.fold_left
              (fun place (name : S.name) -> place / Lir.Field name.text)
              destination (field :: path)
          in
          match value with
          | Some value ->
              let field_ty = type_of st value.id in
              let fresh = temporary st field_ty in
              into st value fresh;
              replace st target field_ty ~by:fresh
          | None -> (
              (* [with (x)] uses the local named [x]. *)
              let resolved = demand st.context Resolve.resolved st.frame.code.definition_key in
              match Option.bind resolved (fun r -> r.names.(field.id)) with
              | Some (Local local) -> (
                  match Hashtbl.find_opt st.frame.bindings local with
                  | Some place ->
                      let field_ty =
                        match st.frame.code.checked.local_types.(local) with
                        | Some ty -> ground st ty
                        | None -> bug "a local with no type"
                      in
                      replace st target field_ty ~by:place
                  | None -> bug "an unbound local in with")
              | _ -> bug "with (x) names no local"))
      | Update_error -> bug "an update that did not parse")
    updates

(* An untagged string with interpolation: each piece written into a
   [TextBuilder], the parts through their [Display]. *)
and interpolate st (literal : S.string_literal) destination =
  let text_path name : Path.t =
    Top { module_ = { package = "standard"; modules = [ "text" ] }; name }
  in
  let builder_ty = Ground.Named { path = text_path "TextBuilder"; arguments = [] } in
  let slice_ty = Ground.Named { path = text_path "StringSlice"; arguments = [] } in
  let method_ name receiver = Path.Method { owner = text_path "TextBuilder"; name; receiver } in
  let call path arguments destination =
    let signature = signature_of st.context path in
    call_instance st
      (Code { path; type_arguments = [] })
      ~signature ~substitution:[] ~arguments ~mask:0 ~destination
  in
  let builder = temporary st builder_ty in
  call (method_ "new" Static) [] builder;
  let unit = Monomorphic.builtin Unit in
  let write text =
    if text <> "" then begin
      let slice = temporary st slice_ty in
      (match Monomorphic.shape st.context.monomorphic slice_ty with
      | Record [ (field, Typed view) ] ->
          emit st.b
            (Assign
               ( slice / Field field,
                 Build
                   {
                     ty = view;
                     variant = None;
                     fields =
                       [
                         ("elements", Constant (Bytes text)); ("length", usize (String.length text));
                       ];
                   } ))
      | _ -> bug "a StringSlice that is not a view");
      call (method_ "write" Mut)
        [ (Mut, builder_ty, builder); (Read, slice_ty, slice) ]
        (temporary st unit)
    end
  in
  write literal.first.value;
  List.iter
    (fun ((part : S.expression), (text : S.text)) ->
      let ty = type_of st part.id in
      let place = expression st part in
      trait_call st
        ~trait:(Top { module_ = { package = "standard"; modules = [ "core" ] }; name = "Display" })
        ~name:"display" ~receiver:Read ~self:ty
        ~arguments:[ (Read, ty, place); (Mut, builder_ty, builder) ]
        ~destination:(temporary st unit);
      write text.value)
    literal.rest;
  call (method_ "finish" Own) [ (Own, builder_ty, builder) ] destination

(* [any value]: the value moved into a block of its own, the one
   allocation an [any] costs, with the table for its type and trait. *)
and any_value st (e : S.expression) (inner : S.expression) destination =
  let any_ty = type_of st e.id in
  let inner_ty = type_of st inner.id in
  let trait, arguments, associated =
    match any_ty with
    | Any { trait; arguments; associated } -> (trait, arguments, associated)
    | _ -> bug "any of %s" (Ground.to_string any_ty)
  in
  let impl, substitution =
    match
      Interface.Impls.implements st.context.database
        ~bounds:(fun _ -> [])
        (back inner_ty)
        {
          trait;
          trait_arguments = List.map back_argument arguments;
          associated = List.map (fun (name, ty) -> (name, back ty)) associated;
        }
    with
    | Some (From_impl { impl; substitution }) -> (impl, substitution)
    | _ -> bug "%s has no impl of %s" (Ground.to_string inner_ty) (Path.show trait)
  in
  let interface = impl_interface st.context impl in
  let type_arguments =
    List.map
      (fun (g : T.generic) ->
        match List.assoc_opt g.generic substitution with
        | Some a -> Monomorphic.ground_argument st.context.monomorphic [] a
        | None -> bug "an unbound parameter of %s" (Path.show impl))
      interface.impl_generics
  in
  (* The value is worked out before its block is made, so that leaving
     early on the way leaves no block behind. *)
  let value = expression st inner in
  let block = local st.b (Raw (Pointer Opaque)) in
  if zero_size st inner_ty then emit st.b (Assign (at block, Use (Constant (Bytes ""))))
  else begin
    emit st.b
      (Call
         {
           target = Intrinsic Allocate;
           arguments = [ Constant (Size_of inner_ty); Constant (Alignment_of inner_ty) ];
           result = Returned (at block);
         });
    let typed = local st.b (Pointer { target = Value inner_ty; writable = true }) in
    emit st.b (Assign (at typed, Use (Copy (at block))));
    emit st.b
      (Assign ({ root = Local typed; projections = [ Deref ] }, Use (owned st value inner_ty)))
  end;
  emit st.b
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

and is_built_in st (e : S.expression) =
  match st.frame.code.checked.calls.(e.id) with
  | Some { callee = Built_in_operator; _ } -> true
  | _ -> false

and echo st place ty span =
  emit st.b (Call { target = Intrinsic Debug_begin; arguments = []; result = Discarded });
  let arguments = if zero_size st ty then [] else [ Lir.Address { place; writable = false } ] in
  emit st.b
    (Call
       {
         target =
           Direct
             {
               function_ = Instance (Debug ty);
               signature = Glue.debug_signature st.context.glue ty;
             };
         arguments;
         result = Discarded;
       });
  let bytes = local st.b (Raw (Pointer Opaque))
  and length = local st.b (Value st.context.types.usize) in
  emit st.b (Call { target = Intrinsic Debug_bytes; arguments = []; result = Returned (at bytes) });
  emit st.b
    (Call { target = Intrinsic Debug_length; arguments = []; result = Returned (at length) });
  emit st.b (Echo { text = Copy (at bytes); length = Copy (at length); site = site st span })

(* A name that is not a place: a variant with no fields, or a constant. *)
and name_value st (e : S.expression) destination =
  match st.frame.code.checked.meanings.(e.id) with
  | Some (Variant_value { type_; variant }) ->
      emit st.b
        (Assign (destination, Build { ty = ground st type_; variant = Some variant; fields = [] }))
  | Some (Global { path; type_arguments }) -> (
      (* A named function as a value: an adapter that takes the
         environment, and ignores it. *)
      match type_of st e.id with
      | Function ty ->
          let function_ =
            Instance.Code
              {
                path;
                type_arguments =
                  List.map
                    (Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution)
                    type_arguments;
              }
          in
          emit st.b
            (Assign
               ( destination,
                 Function_value { code = Instance (Adapter { function_; ty }); environment = None }
               ))
      | ty -> bug "a global of %s" (Ground.to_string ty))
  | Some meaning -> unsupported st e.span "this name as a value: %s" (C.show_meaning meaning)
  | None -> bug "a name with no meaning: %s" (source st e.span)

and return_ st value =
  match st.frame.exit with
  | Some (exit, depth) ->
      (* A [return] in an inlined method ends the method. *)
      (match value with Some e -> ignore (expression st e) | None -> ());
      leave_to st depth;
      finish st.b (Goto exit);
      start st.b (block st.b)
  | None ->
      (match (value, result_place st) with
      | Some e, Some result ->
          clear_result st;
          into st e result
      | Some e, None -> ignore (expression st e)
      | None, _ -> ());
      leave_to st 0;
      finish st.b (return_result st);
      start st.b (block st.b)
