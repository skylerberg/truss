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
          list_of st ty destination ~site:(site st span)
            (List.map (fun (e : S.expression) value -> into st e value) elements)
      | _ -> unsupported st span "a list literal of %s" (Ground.to_string ty))

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
    template_value st template_ty texts ~site:(site st span)
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
        provided_evidence st ~implementation:pointer
          (List.map
             (fun (provided : C.provided) ->
               (provided.capability, provided.impl, provided.arguments))
             (provided_by implementation)))
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
  let function_type =
    match type_of st e.id with Function f -> f | ty -> bug "a lambda of %s" (Ground.to_string ty)
  in
  let captures =
    List.map
      (fun local ->
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
        (local, place, ty))
      (Option.value st.frame.code.checked.captures.(e.id) ~default:[])
  in
  nested_function st ~function_type
    ~output:(match raw_type_of st e.id with Some (T.Function f) -> Some f.output | _ -> None)
    ~captures
    ~bind_capture:(fun inner local place -> Hashtbl.replace inner.frame.bindings local place)
    ~body:(fun inner taken ->
      List.iter2
        (fun (pattern : S.pattern) (place, (mode : Ground.mode), ty) ->
          bind_pattern inner pattern place ty ~owned:(mode = Own))
        parameters taken;
      block_into inner body (result_place inner))
    destination

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
      string_literal st slice_ty text ~destination:slice;
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
  (* The value is evaluated before its block is allocated, so that leaving
     early during the evaluation leaves no block behind. *)
  let value = expression st inner in
  any_into st ~any_ty ~inner_ty ~impl ~type_arguments ~value destination

and is_built_in st (e : S.expression) =
  match st.frame.code.checked.calls.(e.id) with
  | Some { callee = Built_in_operator; _ } -> true
  | _ -> false

and echo st place ty span =
  let output = temporary st Glue.output_ty in
  emit st.b (Assign (output, Storage.empty Glue.output_ty));
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
         arguments = arguments @ [ Address { place = output; writable = true } ];
         result = Discarded;
       });
  emit st.b
    (Echo
       {
         text = Copy (Storage.buffer output);
         length = Copy (Storage.length output);
         site = site st span;
       })

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
