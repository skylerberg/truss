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
  | Storage _ | Handle | Shared _ -> false
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

let project_variant_field place (variant : Memory_layout.variant_shape) field =
  Lowered.project place (Variant_field { variant = variant.name; field })

let drop_members context builder ~project members =
  List.iter
    (fun (name, member) ->
      if needs_drop context member then Emit_c.Ir_builder.emit builder (Drop (project name)))
    members

let drop_elements context builder element ~count ~project =
  if not (is_trivial context element) then
    Emit_c.Ir_builder.emit_loop builder ~count (fun index ->
        Emit_c.Ir_builder.emit builder
          (Drop (project (Lowered.Copy (Lowered.make_local_place index)))))

let drop context ty =
  let builder = Emit_c.Ir_builder.create context.env ~item:(Drop ty) in
  let pointer =
    Emit_c.Ir_builder.allocate_local builder (Pointer { target = Value ty; writable = true })
  in
  let value = Lowered.make_deref_place pointer in
  Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder);
  (match Representation.classify context.env ty with
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
  | Shape (Sum variants) ->
      let after = Emit_c.Ir_builder.allocate_block builder in
      let cases =
        List.filter_map
          (fun (variant_shape : Memory_layout.variant_shape) ->
            if
              variant_shape.indirect
              || List.exists (fun (_, member) -> needs_drop context member) variant_shape.fields
            then begin
              let block = Emit_c.Ir_builder.allocate_block builder in
              Emit_c.Ir_builder.run_in_block builder block (fun () ->
                  drop_members context builder
                    ~project:(project_variant_field value variant_shape)
                    variant_shape.fields;
                  if variant_shape.indirect then
                    Emit_c.Ir_builder.emit builder
                      (Free_block { place = value; variant = variant_shape.name });
                  Emit_c.Ir_builder.finish builder (Goto after));
              Some (variant_shape.name, block)
            end
            else None)
          variants
      in
      Emit_c.Ir_builder.finish builder
        (Switch_variant { place = value; cases; default = Some after });
      Emit_c.Ir_builder.start builder after
  | Shape (Scalar _) -> ());
  Emit_c.Ir_builder.finish builder (Return None);
  Emit_c.Ir_builder.build builder { parameters = [ pointer ]; result = None; returns = true }

let build_untyped_drop context ty =
  let builder = Emit_c.Ir_builder.create context.env ~item:(Untyped_drop ty) in
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

let copy_members context builder ty ~destination ?variant ~project members =
  let fields =
    List.map
      (fun (name, member) -> copy_field context builder ~source:(project name) (name, member))
      members
  in
  Emit_c.Ir_builder.emit builder (Assign (destination, Build { ty; variant; fields }))

let copy_elements context builder element ~count ~destination ~source =
  Emit_c.Ir_builder.emit_loop builder ~count (fun index ->
      let index = Lowered.Copy (Lowered.make_local_place index) in
      copy_into context builder ~destination:(destination index) ~source:(source index) element)

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
  | Shape (Sum variants) ->
      let after = Emit_c.Ir_builder.allocate_block builder in
      let cases =
        List.map
          (fun (variant_shape : Memory_layout.variant_shape) ->
            let block = Emit_c.Ir_builder.allocate_block builder in
            Emit_c.Ir_builder.run_in_block builder block (fun () ->
                copy_members context builder ty ~destination:result ~variant:variant_shape.name
                  ~project:(project_variant_field self variant_shape)
                  variant_shape.fields;
                Emit_c.Ir_builder.finish builder (Goto after));
            (variant_shape.name, block))
          variants
      in
      Emit_c.Ir_builder.finish builder (Switch_variant { place = self; cases; default = None });
      Emit_c.Ir_builder.start builder after);
  Emit_c.Ir_builder.finish builder
    (Return (match result_pointer with Some _ -> None | None -> Some (Move result)));
  Emit_c.Ir_builder.build builder
    {
      parameters = Option.to_list result_pointer @ [ self_local ];
      result = (copy_signature context ty).result;
      returns = true;
    }

module For_testing = struct
  let copy_signature = copy_signature
end
