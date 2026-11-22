let raise_bug format = Compiler_bug.raise_bug ~stage:"Drop_and_copy" format

module Type_map = Map.Make (struct
  type t = Ground.ty

  let compare = Ground.compare
end)

type t = { env : Memory_layout.env; mutable is_trivial_by_type : bool Type_map.t }

let create env = { env; is_trivial_by_type = Type_map.empty }

let rec is_trivial context ty =
  match Type_map.find_opt ty context.is_trivial_by_type with
  | Some is_trivial_ty -> is_trivial_ty
  | None ->
      context.is_trivial_by_type <- Type_map.add ty false context.is_trivial_by_type;
      let is_trivial_ty = has_trivial_representation context ty in
      context.is_trivial_by_type <- Type_map.add ty is_trivial_ty context.is_trivial_by_type;
      is_trivial_ty

and has_trivial_representation context ty =
  let are_trivial fields =
    List.for_all (fun (_, member) -> is_trivial_member context member) fields
  in
  match Representation.classify context.env ty with
  | Storage _ | Handle | Shared _ | Any -> false
  | Shape (Scalar _) -> true
  | Shape (Record fields) -> are_trivial fields
  | Shape (Array (element, _)) -> is_trivial context element
  | Shape (Sum variants) ->
      List.for_all
        (fun (variant : Memory_layout.variant_shape) ->
          (not variant.indirect) && are_trivial variant.fields)
        variants

and is_trivial_member context : Memory_layout.member -> bool = function
  | Typed ty -> is_trivial context ty
  | Raw _ -> true

let needs_drop context member = not (is_trivial_member context member)
let any_drop_slot = 0
let any_copy_slot = 1

let make_box_signature result : Lowered.signature =
  { parameters = [ Raw (Pointer Opaque) ]; result; returns = true }

let any_drop_signature = make_box_signature None
let any_copy_signature = make_box_signature (Some (Raw (Pointer Opaque)))

let list_any_entries ty ~is_copyable =
  (Lowered.Item.Any_drop ty, any_drop_signature)
  :: (if is_copyable then [ (Lowered.Item.Any_copy ty, any_copy_signature) ] else [])

let compute_first_method_slot ~is_copyable =
  if is_copyable then any_copy_slot + 1 else any_drop_slot + 1

let allocate_box context builder ty =
  let layout = Memory_layout.of_type context.env ty in
  let box = Emit_c.Ir_builder.allocate_local builder (Raw (Pointer Opaque)) in
  Emit_c.Ir_builder.emit builder
    (Call
       {
         target = Intrinsic Allocate;
         arguments =
           [
             Lowered.make_uint64_constant layout.size; Lowered.make_uint64_constant layout.alignment;
           ];
         result = Returned (Lowered.make_local_place box);
       });
  box

type recursive_fields = { leading : string list; spine : string option }

let split_recursive_fields ty (variant : Memory_layout.variant_shape) =
  let fields =
    List.filter_map
      (fun (field, (member : Memory_layout.member)) ->
        match member with
        | Typed field_ty when Ground.compare field_ty ty = 0 -> Some field
        | Typed _ | Raw _ -> None)
      variant.fields
  in
  match List.rev fields with
  | [] -> { leading = []; spine = None }
  | spine :: reversed -> { leading = List.rev reversed; spine = Some spine }

let list_recursive_fields ty variants =
  List.map (fun variant -> (variant, split_recursive_fields ty variant)) variants

let is_recursive recursive_fields =
  List.exists (fun (_, (fields : recursive_fields)) -> Option.is_some fields.spine) recursive_fields

let project_variant_field place (variant : Memory_layout.variant_shape) field =
  Lowered.project place (Variant_field { variant = variant.name; field })

let drop_variants context builder ty ~value variants =
  let emit = Emit_c.Ir_builder.emit builder in
  let allocate_value () =
    Lowered.make_local_place (Emit_c.Ir_builder.allocate_local builder (Value ty))
  in
  let recursive_fields = list_recursive_fields ty variants in
  let current =
    if is_recursive recursive_fields then begin
      let current = allocate_value () in
      emit (Assign (current, Use (Move value)));
      current
    end
    else value
  in
  let head = Emit_c.Ir_builder.allocate_block builder in
  let after = Emit_c.Ir_builder.allocate_block builder in
  Emit_c.Ir_builder.finish builder (Goto head);
  let next = lazy (allocate_value ()) in
  let rotation =
    lazy
      (let leading_pointer =
         Emit_c.Ir_builder.allocate_local builder (Pointer { target = Value ty; writable = true })
       in
       let child = allocate_value () in
       let leading_field : Lowered.place =
         { root = Local leading_pointer; projections = [ Deref ] }
       in
       let rotations =
         List.filter_map
           (fun ((variant : Memory_layout.variant_shape), (fields : recursive_fields)) ->
             Option.map
               (fun spine ->
                 let rotate = Emit_c.Ir_builder.allocate_block builder in
                 Emit_c.Ir_builder.run_in_block builder rotate (fun () ->
                     let child_spine = project_variant_field child variant spine in
                     emit (Assign (child, Use (Move leading_field)));
                     emit (Assign (leading_field, Use (Move child_spine)));
                     emit (Assign (child_spine, Use (Move current)));
                     emit (Assign (current, Use (Move child)));
                     Emit_c.Ir_builder.finish builder (Goto head));
                 (variant.name, rotate))
               fields.spine)
           recursive_fields
       in
       (leading_pointer, leading_field, rotations))
  in
  let rotate_if_deep variant field =
    let leading_pointer, leading_field, rotations = Lazy.force rotation in
    let shallow = Emit_c.Ir_builder.allocate_block builder in
    emit
      (Assign
         ( Lowered.make_local_place leading_pointer,
           Use (Address { place = project_variant_field current variant field; writable = true }) ));
    Emit_c.Ir_builder.finish builder
      (Switch_variant { place = leading_field; cases = rotations; default = Some shallow });
    Emit_c.Ir_builder.start builder shallow
  in
  let drop_fields_and_free (variant : Memory_layout.variant_shape) ~spine =
    List.iter
      (fun (field, member) ->
        if Some field <> spine && needs_drop context member then
          emit (Drop (project_variant_field current variant field)))
      variant.fields;
    if variant.indirect then emit (Free_block { place = current; variant = variant.name })
  in
  let build_case (variant : Memory_layout.variant_shape) body =
    let case = Emit_c.Ir_builder.allocate_block builder in
    Emit_c.Ir_builder.run_in_block builder case body;
    Some (variant.name, case)
  in
  let cases =
    List.filter_map
      (fun ((variant : Memory_layout.variant_shape), (fields : recursive_fields)) ->
        match fields.spine with
        | Some spine ->
            build_case variant (fun () ->
                List.iter (rotate_if_deep variant) fields.leading;
                let next = Lazy.force next in
                emit (Assign (next, Use (Move (project_variant_field current variant spine))));
                drop_fields_and_free variant ~spine:fields.spine;
                emit (Assign (current, Use (Move next)));
                Emit_c.Ir_builder.finish builder (Goto head))
        | None
          when variant.indirect
               || List.exists (fun (_, member) -> needs_drop context member) variant.fields ->
            build_case variant (fun () ->
                drop_fields_and_free variant ~spine:fields.spine;
                Emit_c.Ir_builder.finish builder (Goto after))
        | None -> None)
      recursive_fields
  in
  Emit_c.Ir_builder.start builder head;
  Emit_c.Ir_builder.finish builder (Switch_variant { place = current; cases; default = Some after });
  Emit_c.Ir_builder.start builder after

let drop context ty =
  let builder = Emit_c.Ir_builder.create context.env ~item:(Drop ty) in
  let pointer =
    Emit_c.Ir_builder.allocate_local builder (Pointer { target = Value ty; writable = true })
  in
  let value : Lowered.place = { root = Local pointer; projections = [ Deref ] } in
  Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder);
  (match Representation.classify context.env ty with
  | Any ->
      Emit_c.Ir_builder.emit builder
        (Call
           {
             target =
               Table_call
                 {
                   table = Copy (Builtin_records.Any.project_vtable value);
                   value = Copy (Builtin_records.Any.project_value value);
                   slot = any_drop_slot;
                   signature = any_drop_signature;
                 };
             arguments = [];
             result = Discarded;
           });
      Emit_c.Ir_builder.emit builder
        (Call
           {
             target = Intrinsic Free;
             arguments = [ Copy (Builtin_records.Any.project_value value) ];
             result = Discarded;
           })
  | Handle ->
      Emit_c.Ir_builder.emit builder
        (Call
           {
             target = Foreign (Libc.make_declaration (Memory_layout.system context.env) Close);
             arguments = [ Copy (Builtin_records.Handle.project_descriptor value) ];
             result = Discarded;
           })
  | Shared inner ->
      let pointer = Lowered.Copy (Builtin_records.Shared.project_value value) in
      let is_last = Emit_c.Ir_builder.allocate_local builder (Raw Bool) in
      Emit_c.Ir_builder.emit builder
        (Call
           {
             target = Intrinsic Shared_release;
             arguments = [ pointer ];
             result = Returned (Lowered.make_local_place is_last);
           });
      Emit_c.Ir_builder.emit_when builder
        (Holds (Copy (Lowered.make_local_place is_last)))
        (fun () ->
          if not (is_trivial context inner) then begin
            let typed =
              Emit_c.Ir_builder.allocate_local builder
                (Pointer { target = Value inner; writable = true })
            in
            Emit_c.Ir_builder.emit builder (Assign (Lowered.make_local_place typed, Use pointer));
            Emit_c.Ir_builder.emit builder
              (Call
                 {
                   target =
                     Direct
                       {
                         function_ = Item (Drop inner);
                         signature = Convention.drop_signature inner;
                       };
                   arguments = [ Copy (Lowered.make_local_place typed) ];
                   result = Discarded;
                 })
          end;
          Emit_c.Ir_builder.emit builder
            (Call { target = Intrinsic Shared_free; arguments = [ pointer ]; result = Discarded }))
  | Storage element ->
      if not (is_trivial context element) then
        Emit_c.Ir_builder.emit_loop builder
          ~count:(Copy (Storage.project_length value))
          (fun index ->
            Emit_c.Ir_builder.emit builder
              (Drop (Storage.index_element value (Copy (Lowered.make_local_place index)))));
      Emit_c.Ir_builder.emit_when builder
        (Test (Storage.make_owned_block_test value))
        (fun () ->
          Emit_c.Ir_builder.emit builder
            (Call
               {
                 target = Intrinsic Free;
                 arguments = [ Copy (Storage.project_buffer value) ];
                 result = Discarded;
               }))
  | Shape (Record fields) ->
      List.iter
        (fun (name, member) ->
          if needs_drop context member then
            Emit_c.Ir_builder.emit builder (Drop (Lowered.project value (Field name))))
        fields
  | Shape (Array (element, count)) ->
      if not (is_trivial context element) then
        Emit_c.Ir_builder.emit_loop builder ~count:(Lowered.make_uint64_constant count)
          (fun index ->
            Emit_c.Ir_builder.emit builder
              (Drop (Lowered.project value (Index (Copy (Lowered.make_local_place index))))))
  | Shape (Sum variants) -> drop_variants context builder ty ~value variants
  | Shape (Scalar _) -> ());
  Emit_c.Ir_builder.finish builder (Return None);
  Emit_c.Ir_builder.build builder { parameters = [ pointer ]; result = None; returns = true }

let build_any_drop context ty =
  let builder = Emit_c.Ir_builder.create context.env ~item:(Any_drop ty) in
  let untyped = Emit_c.Ir_builder.allocate_local builder (Raw (Pointer Opaque)) in
  Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder);
  if not (is_trivial context ty) then begin
    let typed =
      Emit_c.Ir_builder.allocate_local builder (Pointer { target = Value ty; writable = true })
    in
    Emit_c.Ir_builder.emit builder
      (Assign (Lowered.make_local_place typed, Use (Copy (Lowered.make_local_place untyped))));
    Emit_c.Ir_builder.emit builder
      (Call
         {
           target = Direct { function_ = Item (Drop ty); signature = Convention.drop_signature ty };
           arguments = [ Copy (Lowered.make_local_place typed) ];
           result = Discarded;
         })
  end;
  Emit_c.Ir_builder.finish builder (Return None);
  Emit_c.Ir_builder.build builder { parameters = [ untyped ]; result = None; returns = true }

let copy_signature context ty : Lowered.signature =
  Convention.make_signature
    (Option.to_list (Convention.classify_parameter context.env Read ty))
    (Convention.classify_result context.env ty)

let copy_into context builder ~destination ~source ty =
  if is_trivial context ty then
    Emit_c.Ir_builder.emit builder (Assign (destination, Use (Copy source)))
  else
    let arguments =
      match Convention.classify_parameter context.env Read ty with
      | Some (Pointer _) -> [ Lowered.Address { place = source; writable = false } ]
      | Some _ -> [ Lowered.Copy source ]
      | None -> []
    in
    Emit_c.Ir_builder.emit builder
      (Call
         {
           target = Direct { function_ = Item (Copy ty); signature = copy_signature context ty };
           arguments;
           result =
             Convention.make_destination (Convention.classify_result context.env ty) destination;
         })

let copy_field context builder ~source (name, member) =
  match member with
  | Memory_layout.Raw _ -> (name, Lowered.Copy source)
  | Typed ty when is_trivial context ty -> (name, Lowered.Copy source)
  | Typed ty ->
      let temporary = Emit_c.Ir_builder.allocate_local builder (Value ty) in
      copy_into context builder ~destination:(Lowered.make_local_place temporary) ~source ty;
      (name, Lowered.Move (Lowered.make_local_place temporary))

let copy_variants context builder ty ~self ~result variants =
  let emit = Emit_c.Ir_builder.emit builder in
  let head = Emit_c.Ir_builder.allocate_block builder in
  let after = Emit_c.Ir_builder.allocate_block builder in
  let recursive_fields = list_recursive_fields ty variants in
  let source, destination, finish_case =
    if is_recursive recursive_fields then begin
      let allocate_pointer ~writable =
        Emit_c.Ir_builder.allocate_local builder (Pointer { target = Value ty; writable })
      in
      let source_pointer = allocate_pointer ~writable:false in
      let destination_pointer = allocate_pointer ~writable:true in
      let point pointer place ~writable =
        emit (Assign (Lowered.make_local_place pointer, Use (Address { place; writable })))
      in
      point source_pointer self ~writable:false;
      point destination_pointer result ~writable:true;
      let source : Lowered.place = { root = Local source_pointer; projections = [ Deref ] } in
      let destination : Lowered.place =
        { root = Local destination_pointer; projections = [ Deref ] }
      in
      let follow_spine variant = function
        | None -> Emit_c.Ir_builder.finish builder (Goto after)
        | Some spine ->
            point destination_pointer
              (project_variant_field destination variant spine)
              ~writable:true;
            point source_pointer (project_variant_field source variant spine) ~writable:false;
            Emit_c.Ir_builder.finish builder (Goto head)
      in
      (source, destination, follow_spine)
    end
    else (self, result, fun _ _ -> Emit_c.Ir_builder.finish builder (Goto after))
  in
  Emit_c.Ir_builder.finish builder (Goto head);
  let cases =
    List.map
      (fun ((variant : Memory_layout.variant_shape), (fields : recursive_fields)) ->
        let case = Emit_c.Ir_builder.allocate_block builder in
        Emit_c.Ir_builder.run_in_block builder case (fun () ->
            let copied =
              List.filter_map
                (fun (name, member) ->
                  if Some name = fields.spine then None
                  else
                    Some
                      (copy_field context builder
                         ~source:(project_variant_field source variant name)
                         (name, member)))
                variant.fields
            in
            emit (Assign (destination, Build { ty; variant = Some variant.name; fields = copied }));
            finish_case variant fields.spine);
        (variant.name, case))
      recursive_fields
  in
  Emit_c.Ir_builder.start builder head;
  Emit_c.Ir_builder.finish builder (Switch_variant { place = source; cases; default = None });
  Emit_c.Ir_builder.start builder after

let copy context ty =
  let builder = Emit_c.Ir_builder.create context.env ~item:(Copy ty) in
  let convention = Convention.classify_result context.env ty in
  let result_pointer =
    match convention with
    | Through_pointer pointer -> Some (Emit_c.Ir_builder.allocate_local builder pointer)
    | Returned _ | Nothing -> None
  in
  let parameter = Convention.classify_parameter context.env Read ty in
  let self_local = Option.map (fun ty -> Emit_c.Ir_builder.allocate_local builder ty) parameter in
  let self : Lowered.place =
    match (parameter, self_local) with
    | Some (Pointer _), Some local -> { root = Local local; projections = [ Deref ] }
    | Some _, Some local -> Lowered.make_local_place local
    | _ -> Lowered.make_local_place 0
  in
  let result_local =
    match result_pointer with
    | None -> Some (Emit_c.Ir_builder.allocate_local builder (Value ty))
    | Some _ -> None
  in
  let result : Lowered.place =
    match (result_pointer, result_local) with
    | Some pointer, _ -> { root = Local pointer; projections = [ Deref ] }
    | None, Some local -> Lowered.make_local_place local
    | None, None -> raise_bug "no place for the copy"
  in
  Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder);
  (match Representation.classify context.env ty with
  | Handle -> raise_bug "a copy of a handle, which is not Copyable"
  | Any ->
      let copied = Emit_c.Ir_builder.allocate_local builder (Raw (Pointer Opaque)) in
      Emit_c.Ir_builder.emit builder
        (Call
           {
             target =
               Table_call
                 {
                   table = Copy (Builtin_records.Any.project_vtable self);
                   value = Copy (Builtin_records.Any.project_value self);
                   slot = any_copy_slot;
                   signature = any_copy_signature;
                 };
             arguments = [];
             result = Returned (Lowered.make_local_place copied);
           });
      Emit_c.Ir_builder.emit builder
        (Assign
           ( result,
             Builtin_records.Any.build ty
               ~value:(Copy (Lowered.make_local_place copied))
               ~vtable:(Copy (Builtin_records.Any.project_vtable self)) ))
  | Shape (Scalar _) -> raise_bug "a copy of the scalar %s, which is trivial" (Ground.to_string ty)
  | Shared _ ->
      Emit_c.Ir_builder.emit builder
        (Call
           {
             target = Intrinsic Shared_retain;
             arguments = [ Copy (Builtin_records.Shared.project_value self) ];
             result = Discarded;
           });
      Emit_c.Ir_builder.emit builder (Assign (result, Use (Copy self)))
  | Storage element ->
      let layout = Memory_layout.of_type context.env element in
      let multiply_by_size count =
        Emit_c.Ir_builder.emit_value builder (Raw (Integer UInt64))
          (Binary (Multiply, count, Lowered.make_uint64_constant layout.size))
      in
      Emit_c.Ir_builder.emit_if builder
        (Test (Storage.make_owned_block_test self))
        ~yes:(fun () ->
          let bytes = multiply_by_size (Copy (Storage.project_capacity self)) in
          let buffer = Emit_c.Ir_builder.allocate_local builder (Raw (Pointer (Data element))) in
          Emit_c.Ir_builder.emit builder
            (Call
               {
                 target = Intrinsic Allocate;
                 arguments = [ bytes; Lowered.make_uint64_constant layout.alignment ];
                 result = Returned (Lowered.make_local_place buffer);
               });
          if is_trivial context element then
            Emit_c.Ir_builder.emit builder
              (Call
                 {
                   target = Intrinsic Copy_bytes;
                   arguments =
                     [
                       Copy (Lowered.make_local_place buffer);
                       Copy (Storage.project_buffer self);
                       multiply_by_size (Copy (Storage.project_length self));
                     ];
                   result = Discarded;
                 })
          else
            Emit_c.Ir_builder.emit_loop builder
              ~count:(Copy (Storage.project_length self))
              (fun index ->
                copy_into context builder
                  ~destination:
                    (Lowered.project (Lowered.make_local_place buffer)
                       (Index (Copy (Lowered.make_local_place index))))
                  ~source:(Storage.index_element self (Copy (Lowered.make_local_place index)))
                  element);
          Emit_c.Ir_builder.emit builder
            (Assign
               ( result,
                 Storage.build_storage ty
                   ~buffer:(Copy (Lowered.make_local_place buffer))
                   ~length:(Copy (Storage.project_length self))
                   ~capacity:(Copy (Storage.project_capacity self)) )))
        ~no:(fun () -> Emit_c.Ir_builder.emit builder (Assign (result, Storage.build_empty ty)))
  | Shape (Record fields) ->
      let fields =
        List.map
          (fun (name, member) ->
            copy_field context builder ~source:(Lowered.project self (Field name)) (name, member))
          fields
      in
      Emit_c.Ir_builder.emit builder (Assign (result, Build { ty; variant = None; fields }))
  | Shape (Array (element, count)) ->
      Emit_c.Ir_builder.emit_loop builder ~count:(Lowered.make_uint64_constant count) (fun index ->
          copy_into context builder
            ~destination:(Lowered.project result (Index (Copy (Lowered.make_local_place index))))
            ~source:(Lowered.project self (Index (Copy (Lowered.make_local_place index))))
            element)
  | Shape (Sum variants) -> copy_variants context builder ty ~self ~result variants);
  (match result_local with
  | Some local ->
      Emit_c.Ir_builder.finish builder (Return (Some (Move (Lowered.make_local_place local))))
  | None -> Emit_c.Ir_builder.finish builder (Return None));
  let parameters = Option.to_list result_pointer @ Option.to_list self_local in
  Emit_c.Ir_builder.build builder
    {
      parameters;
      result =
        (match convention with Returned ty -> Some ty | Nothing | Through_pointer _ -> None);
      returns = true;
    }

let build_any_copy context ty =
  let builder = Emit_c.Ir_builder.create context.env ~item:(Any_copy ty) in
  let original = Emit_c.Ir_builder.allocate_local builder (Raw (Pointer Opaque)) in
  Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder);
  let copied = allocate_box context builder ty in
  if not (Memory_layout.has_zero_size context.env ty) then begin
    let source =
      Emit_c.Ir_builder.allocate_local builder (Pointer { target = Value ty; writable = false })
    in
    let destination =
      Emit_c.Ir_builder.allocate_local builder (Pointer { target = Value ty; writable = true })
    in
    Emit_c.Ir_builder.emit builder
      (Assign (Lowered.make_local_place source, Use (Copy (Lowered.make_local_place original))));
    Emit_c.Ir_builder.emit builder
      (Assign (Lowered.make_local_place destination, Use (Copy (Lowered.make_local_place copied))));
    copy_into context builder
      ~destination:{ root = Local destination; projections = [ Deref ] }
      ~source:{ root = Local source; projections = [ Deref ] }
      ty
  end;
  Emit_c.Ir_builder.finish builder (Return (Some (Copy (Lowered.make_local_place copied))));
  Emit_c.Ir_builder.build builder
    { parameters = [ original ]; result = Some (Raw (Pointer Opaque)); returns = true }

module For_testing = struct
  let copy_signature = copy_signature
end
