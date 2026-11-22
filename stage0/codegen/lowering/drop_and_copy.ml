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
  | Shape (Array (_, 0)) -> true
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

let project_variant_field place (variant : Memory_layout.variant_shape) field =
  Lowered.project place (Variant_field { variant = variant.name; field })

let emit_spine_loop builder ty ~scrutinee variants emit_case =
  let head = Emit_c.Ir_builder.allocate_block builder in
  let after = Emit_c.Ir_builder.allocate_block builder in
  let emit_case = emit_case ~head in
  Emit_c.Ir_builder.finish builder (Goto head);
  let cases =
    List.map
      (fun (variant : Memory_layout.variant_shape) ->
        let fields = split_recursive_fields ty variant in
        let case = Emit_c.Ir_builder.allocate_block builder in
        Emit_c.Ir_builder.run_in_block builder case (fun () ->
            emit_case variant fields;
            Emit_c.Ir_builder.finish builder
              (Goto (if Option.is_some fields.spine then head else after)));
        (variant.name, case))
      variants
  in
  Emit_c.Ir_builder.start builder head;
  Emit_c.Ir_builder.finish builder (Switch_variant { place = scrutinee; cases; default = None });
  Emit_c.Ir_builder.start builder after

let drop_members context builder ~project ?except members =
  List.iter
    (fun (name, member) ->
      if Some name <> except && needs_drop context member then
        Emit_c.Ir_builder.emit builder (Drop (project name)))
    members

let drop_elements context builder element ~count ~project =
  if not (is_trivial context element) then
    Emit_c.Ir_builder.emit_loop builder ~count (fun index ->
        Emit_c.Ir_builder.emit builder
          (Drop (project (Lowered.Copy (Lowered.make_local_place index)))))

let drop_variants context builder ty ~value variants =
  let emit = Emit_c.Ir_builder.emit builder in
  let detached =
    lazy (Lowered.make_local_place (Emit_c.Ir_builder.allocate_local builder (Value ty)))
  in
  emit_spine_loop builder ty ~scrutinee:value variants (fun ~head ->
      let rotate_if_deep =
        lazy
          (let leading_pointer =
             Emit_c.Ir_builder.allocate_local builder
               (Pointer { target = Value ty; writable = true })
           in
           let leading_field = Lowered.make_deref_place leading_pointer in
           let detached = Lazy.force detached in
           let rotations =
             List.filter_map
               (fun (variant : Memory_layout.variant_shape) ->
                 Option.map
                   (fun spine ->
                     let rotate = Emit_c.Ir_builder.allocate_block builder in
                     Emit_c.Ir_builder.run_in_block builder rotate (fun () ->
                         let detached_spine = project_variant_field detached variant spine in
                         emit (Assign (detached, Use (Move leading_field)));
                         emit (Assign (leading_field, Use (Move detached_spine)));
                         emit (Assign (detached_spine, Use (Move value)));
                         emit (Assign (value, Use (Move detached)));
                         Emit_c.Ir_builder.finish builder (Goto head));
                     (variant.name, rotate))
                   (split_recursive_fields ty variant).spine)
               variants
           in
           fun variant field ->
             let shallow = Emit_c.Ir_builder.allocate_block builder in
             emit
               (Assign
                  ( Lowered.make_local_place leading_pointer,
                    Use
                      (Address
                         { place = project_variant_field value variant field; writable = true }) ));
             Emit_c.Ir_builder.finish builder
               (Switch_variant { place = leading_field; cases = rotations; default = Some shallow });
             Emit_c.Ir_builder.start builder shallow)
      in
      fun variant fields ->
        List.iter (fun field -> Lazy.force rotate_if_deep variant field) fields.leading;
        let node =
          match fields.spine with
          | None -> value
          | Some spine ->
              let detached = Lazy.force detached in
              emit (Assign (detached, Use (Move value)));
              emit (Assign (value, Use (Move (project_variant_field detached variant spine))));
              detached
        in
        drop_members context builder
          ~project:(project_variant_field node variant)
          ?except:fields.spine variant.fields;
        if variant.indirect then emit (Free_block { place = node; variant = variant.name }))

let drop context ty =
  let builder = Emit_c.Ir_builder.create context.env ~item:(Drop ty) in
  let pointer =
    Emit_c.Ir_builder.allocate_local builder (Pointer { target = Value ty; writable = true })
  in
  let value = Lowered.make_deref_place pointer in
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
            Emit_c.Ir_builder.emit builder (Drop (Lowered.make_deref_place typed))
          end;
          Emit_c.Ir_builder.emit builder
            (Call { target = Intrinsic Shared_free; arguments = [ pointer ]; result = Discarded }))
  | Storage element ->
      drop_elements context builder element
        ~count:(Copy (Storage.project_length value))
        ~project:(Storage.index_element value);
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
      drop_members context builder ~project:(fun name -> Lowered.project value (Field name)) fields
  | Shape (Array (element, count)) ->
      drop_elements context builder element ~count:(Lowered.make_uint64_constant count)
        ~project:(fun index -> Lowered.project value (Index index))
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
    Emit_c.Ir_builder.emit builder (Drop (Lowered.make_deref_place typed))
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

let copy_members context builder ty ~destination ?variant ?except ~project members =
  let fields =
    List.filter_map
      (fun (name, member) ->
        if Some name = except then None
        else Some (copy_field context builder ~source:(project name) (name, member)))
      members
  in
  Emit_c.Ir_builder.emit builder (Assign (destination, Build { ty; variant; fields }))

let copy_elements context builder element ~count ~destination ~source =
  Emit_c.Ir_builder.emit_loop builder ~count (fun index ->
      let index = Lowered.Copy (Lowered.make_local_place index) in
      copy_into context builder ~destination:(destination index) ~source:(source index) element)

let copy_variants context builder ty ~self ~result variants =
  let point pointer place ~writable =
    Emit_c.Ir_builder.emit builder
      (Assign (Lowered.make_local_place pointer, Use (Address { place; writable })))
  in
  let allocate_pointer_to place ~writable =
    let pointer =
      Emit_c.Ir_builder.allocate_local builder (Pointer { target = Value ty; writable })
    in
    point pointer place ~writable;
    pointer
  in
  let source_pointer = allocate_pointer_to self ~writable:false in
  let destination_pointer = allocate_pointer_to result ~writable:true in
  let source = Lowered.make_deref_place source_pointer in
  let destination = Lowered.make_deref_place destination_pointer in
  emit_spine_loop builder ty ~scrutinee:source variants (fun ~head:_ variant fields ->
      copy_members context builder ty ~destination ~variant:variant.name ?except:fields.spine
        ~project:(project_variant_field source variant)
        variant.fields;
      Option.iter
        (fun spine ->
          point destination_pointer (project_variant_field destination variant spine) ~writable:true;
          point source_pointer (project_variant_field source variant spine) ~writable:false)
        fields.spine)

let copy context ty =
  let builder = Emit_c.Ir_builder.create context.env ~item:(Copy ty) in
  let raise_zero_size () =
    raise_bug "a copy of %s, which has zero size and so is trivial" (Ground.to_string ty)
  in
  let result_pointer, result =
    match Convention.classify_result context.env ty with
    | Through_pointer pointer ->
        let pointer = Emit_c.Ir_builder.allocate_local builder pointer in
        (Some pointer, Lowered.make_deref_place pointer)
    | Returned _ ->
        (None, Lowered.make_local_place (Emit_c.Ir_builder.allocate_local builder (Value ty)))
    | Nothing -> raise_zero_size ()
  in
  let self_local, self =
    match Convention.classify_parameter context.env Read ty with
    | Some (Pointer _ as parameter) ->
        let local = Emit_c.Ir_builder.allocate_local builder parameter in
        (local, Lowered.make_deref_place local)
    | Some parameter ->
        let local = Emit_c.Ir_builder.allocate_local builder parameter in
        (local, Lowered.make_local_place local)
    | None -> raise_zero_size ()
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
            copy_elements context builder element
              ~count:(Copy (Storage.project_length self))
              ~destination:(fun index ->
                Lowered.project (Lowered.make_local_place buffer) (Index index))
              ~source:(Storage.index_element self);
          Emit_c.Ir_builder.emit builder
            (Assign
               ( result,
                 Storage.build_storage ty
                   ~buffer:(Copy (Lowered.make_local_place buffer))
                   ~length:(Copy (Storage.project_length self))
                   ~capacity:(Copy (Storage.project_capacity self)) )))
        ~no:(fun () -> Emit_c.Ir_builder.emit builder (Assign (result, Storage.build_empty ty)))
  | Shape (Record fields) ->
      copy_members context builder ty ~destination:result
        ~project:(fun name -> Lowered.project self (Field name))
        fields
  | Shape (Array (element, count)) ->
      copy_elements context builder element
        ~count:(Lowered.make_uint64_constant count)
        ~destination:(fun index -> Lowered.project result (Index index))
        ~source:(fun index -> Lowered.project self (Index index))
  | Shape (Sum variants) -> copy_variants context builder ty ~self ~result variants);
  Emit_c.Ir_builder.finish builder
    (Return (match result_pointer with Some _ -> None | None -> Some (Move result)));
  Emit_c.Ir_builder.build builder
    {
      parameters = Option.to_list result_pointer @ [ self_local ];
      result = (copy_signature context ty).result;
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
      ~destination:(Lowered.make_deref_place destination)
      ~source:(Lowered.make_deref_place source) ty
  end;
  Emit_c.Ir_builder.finish builder (Return (Some (Copy (Lowered.make_local_place copied))));
  Emit_c.Ir_builder.build builder
    { parameters = [ original ]; result = Some (Raw (Pointer Opaque)); returns = true }

module For_testing = struct
  let copy_signature = copy_signature
end
