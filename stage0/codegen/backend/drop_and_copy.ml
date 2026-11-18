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

let emit_condition builder rvalue =
  let flag = Emit_c.Ir_builder.allocate_local builder (Raw Bool) in
  Emit_c.Ir_builder.emit builder (Assign (Lowered.make_local_place flag, rvalue));
  Lowered.Copy (Lowered.make_local_place flag)

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
                   table = Copy (Lowered.project value (Field "vtable"));
                   value = Copy (Lowered.project value (Field "value"));
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
             arguments = [ Copy (Lowered.project value (Field "value")) ];
             result = Discarded;
           })
  | Handle ->
      Emit_c.Ir_builder.emit builder
        (Call
           {
             target = Foreign (Libc.make_declaration (Memory_layout.system context.env) Close);
             arguments = [ Copy (Lowered.project value (Field "descriptor")) ];
             result = Discarded;
           })
  | Shared inner ->
      let pointer = Lowered.Copy (Lowered.project value (Field "value")) in
      let is_last = Emit_c.Ir_builder.allocate_local builder (Raw Bool) in
      Emit_c.Ir_builder.emit builder
        (Call
           {
             target = Intrinsic Shared_release;
             arguments = [ pointer ];
             result = Returned (Lowered.make_local_place is_last);
           });
      Emit_c.Ir_builder.emit_when builder
        (Copy (Lowered.make_local_place is_last))
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
        (emit_condition builder (Storage.build_is_allocated value))
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
                  List.iter
                    (fun (field, member) ->
                      if needs_drop context member then
                        Emit_c.Ir_builder.emit builder
                          (Drop
                             (Lowered.project value
                                (Variant_field { variant = variant_shape.name; field }))))
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
                   table = Copy (Lowered.project self (Field "vtable"));
                   value = Copy (Lowered.project self (Field "value"));
                   slot = any_copy_slot;
                   signature = any_copy_signature;
                 };
             arguments = [];
             result = Returned (Lowered.make_local_place copied);
           });
      Emit_c.Ir_builder.emit builder
        (Assign
           ( result,
             Build
               {
                 ty;
                 variant = None;
                 fields =
                   [
                     ("value", Copy (Lowered.make_local_place copied));
                     ("vtable", Copy (Lowered.project self (Field "vtable")));
                   ];
               } ))
  | Shape (Scalar _) -> raise_bug "a copy of the scalar %s, which is trivial" (Ground.to_string ty)
  | Shared _ ->
      Emit_c.Ir_builder.emit builder
        (Call
           {
             target = Intrinsic Shared_retain;
             arguments = [ Copy (Lowered.project self (Field "value")) ];
             result = Discarded;
           });
      Emit_c.Ir_builder.emit builder (Assign (result, Use (Copy self)))
  | Storage element ->
      let layout = Memory_layout.of_type context.env element in
      let unallocated = Emit_c.Ir_builder.allocate_block builder
      and allocate = Emit_c.Ir_builder.allocate_block builder
      and after = Emit_c.Ir_builder.allocate_block builder in
      Emit_c.Ir_builder.branch builder
        (emit_condition builder (Storage.build_is_allocated self))
        ~yes:allocate ~no:unallocated;
      Emit_c.Ir_builder.start builder unallocated;
      Emit_c.Ir_builder.emit builder (Assign (result, Storage.build_empty ty));
      Emit_c.Ir_builder.finish builder (Goto after);
      Emit_c.Ir_builder.start builder allocate;
      let bytes = Emit_c.Ir_builder.allocate_local builder (Raw (Integer UInt64)) in
      let buffer = Emit_c.Ir_builder.allocate_local builder (Raw (Pointer (Data element))) in
      Emit_c.Ir_builder.emit builder
        (Assign
           ( Lowered.make_local_place bytes,
             Binary
               ( Multiply,
                 Copy (Storage.project_capacity self),
                 Lowered.make_uint64_constant layout.size ) ));
      Emit_c.Ir_builder.emit builder
        (Call
           {
             target = Intrinsic Allocate;
             arguments =
               [
                 Copy (Lowered.make_local_place bytes);
                 Lowered.make_uint64_constant layout.alignment;
               ];
             result = Returned (Lowered.make_local_place buffer);
           });
      if is_trivial context element then begin
        let used = Emit_c.Ir_builder.allocate_local builder (Raw (Integer UInt64)) in
        Emit_c.Ir_builder.emit builder
          (Assign
             ( Lowered.make_local_place used,
               Binary
                 ( Multiply,
                   Copy (Storage.project_length self),
                   Lowered.make_uint64_constant layout.size ) ));
        Emit_c.Ir_builder.emit builder
          (Call
             {
               target = Intrinsic Copy_bytes;
               arguments =
                 [
                   Copy (Lowered.make_local_place buffer);
                   Copy (Storage.project_buffer self);
                   Copy (Lowered.make_local_place used);
                 ];
               result = Discarded;
             })
      end
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
               ~capacity:(Copy (Storage.project_capacity self)) ));
      Emit_c.Ir_builder.finish builder (Goto after);
      Emit_c.Ir_builder.start builder after
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
  | Shape (Sum variants) ->
      let after = Emit_c.Ir_builder.allocate_block builder in
      let cases =
        List.map
          (fun (variant_shape : Memory_layout.variant_shape) ->
            let block = Emit_c.Ir_builder.allocate_block builder in
            Emit_c.Ir_builder.run_in_block builder block (fun () ->
                let fields =
                  List.map
                    (fun (name, member) ->
                      copy_field context builder
                        ~source:
                          (Lowered.project self
                             (Variant_field { variant = variant_shape.name; field = name }))
                        (name, member))
                    variant_shape.fields
                in
                Emit_c.Ir_builder.emit builder
                  (Assign (result, Build { ty; variant = Some variant_shape.name; fields }));
                Emit_c.Ir_builder.finish builder (Goto after));
            (variant_shape.name, block))
          variants
      in
      Emit_c.Ir_builder.finish builder (Switch_variant { place = self; cases; default = None });
      Emit_c.Ir_builder.start builder after);
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
