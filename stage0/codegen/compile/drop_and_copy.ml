let bug format = Compiler_bug.bug ~stage:"Drop_and_copy" format

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

let box_signature result : Lowered.signature =
  { parameters = [ Raw (Pointer Opaque) ]; result; returns = true }

let any_drop_signature = box_signature None
let any_copy_signature = box_signature (Some (Raw (Pointer Opaque)))

let any_entries ty ~is_copyable =
  (Instance.Any_drop ty, any_drop_signature)
  :: (if is_copyable then [ (Instance.Any_copy ty, any_copy_signature) ] else [])

let first_method_slot ~is_copyable = if is_copyable then any_copy_slot + 1 else any_drop_slot + 1

module Builder = Emit_c.Builder

let box context builder ty =
  let layout = Memory_layout.of_type context.env ty in
  let box = Builder.local builder ~name:"box" (Raw (Pointer Opaque)) in
  Builder.emit builder
    (Call
       {
         target = Intrinsic Allocate;
         arguments =
           [ Builder.constant_uint64 layout.size; Builder.constant_uint64 layout.alignment ];
         result = Returned (Builder.at box);
       });
  box

let condition builder rvalue =
  let flag = Builder.local builder (Raw Bool) in
  Builder.emit builder (Assign (Builder.at flag, rvalue));
  Lowered.Copy (Builder.at flag)

let drop context ty =
  let builder = Builder.create context.env ~key:(Drop ty) in
  let pointer =
    Builder.local builder ~name:"value" (Pointer { target = Value ty; writable = true })
  in
  let value : Lowered.place = { root = Local pointer; projections = [ Deref ] } in
  Builder.start builder (Builder.block builder);
  (match Representation.classify context.env ty with
  | Any ->
      Builder.emit builder
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
      Builder.emit builder
        (Call
           {
             target = Intrinsic Free;
             arguments = [ Copy (Lowered.project value (Field "value")) ];
             result = Discarded;
           })
  | Handle ->
      Builder.emit builder
        (Call
           {
             target = Foreign (Libc.declaration (Memory_layout.system context.env) Close);
             arguments = [ Copy (Lowered.project value (Field "descriptor")) ];
             result = Discarded;
           })
  | Shared inner ->
      let pointer = Lowered.Copy (Lowered.project value (Field "value")) in
      let is_last = Builder.local builder (Raw Bool) in
      Builder.emit builder
        (Call
           {
             target = Intrinsic Shared_release;
             arguments = [ pointer ];
             result = Returned (Builder.at is_last);
           });
      Builder.when_ builder
        (Copy (Builder.at is_last))
        (fun () ->
          if not (is_trivial context inner) then begin
            let typed = Builder.local builder (Pointer { target = Value inner; writable = true }) in
            Builder.emit builder (Assign (Builder.at typed, Use pointer));
            Builder.emit builder
              (Call
                 {
                   target =
                     Direct
                       {
                         function_ = Instance (Drop inner);
                         signature = Convention.drop_signature inner;
                       };
                   arguments = [ Copy (Builder.at typed) ];
                   result = Discarded;
                 })
          end;
          Builder.emit builder
            (Call { target = Intrinsic Shared_free; arguments = [ pointer ]; result = Discarded }))
  | Storage element ->
      if not (is_trivial context element) then
        Builder.loop builder
          ~count:(Copy (Storage.project_length value))
          (fun index ->
            Builder.emit builder (Drop (Storage.index_element value (Copy (Builder.at index)))));
      Builder.when_ builder
        (condition builder (Storage.build_is_allocated value))
        (fun () ->
          Builder.emit builder
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
            Builder.emit builder (Drop (Lowered.project value (Field name))))
        fields
  | Shape (Array (element, count)) ->
      if not (is_trivial context element) then
        Builder.loop builder ~count:(Builder.constant_uint64 count) (fun index ->
            Builder.emit builder (Drop (Lowered.project value (Index (Copy (Builder.at index))))))
  | Shape (Sum variants) ->
      let after = Builder.block builder in
      let cases =
        List.filter_map
          (fun (variant_shape : Memory_layout.variant_shape) ->
            if
              variant_shape.indirect
              || List.exists (fun (_, member) -> needs_drop context member) variant_shape.fields
            then begin
              let block = Builder.block builder in
              Builder.in_block builder block (fun () ->
                  List.iter
                    (fun (field, member) ->
                      if needs_drop context member then
                        Builder.emit builder
                          (Drop
                             (Lowered.project value
                                (Variant_field { variant = variant_shape.name; field }))))
                    variant_shape.fields;
                  if variant_shape.indirect then
                    Builder.emit builder
                      (Free_block { place = value; variant = variant_shape.name });
                  Builder.finish builder (Goto after));
              Some (variant_shape.name, block)
            end
            else None)
          variants
      in
      Builder.finish builder (Switch_variant { place = value; cases; default = Some after });
      Builder.start builder after
  | Shape (Scalar _) -> ());
  Builder.finish builder (Return None);
  Builder.build builder { parameters = [ pointer ]; result = None; returns = true }

let any_drop context ty =
  let builder = Builder.create context.env ~key:(Any_drop ty) in
  let untyped = Builder.local builder ~name:"value" (Raw (Pointer Opaque)) in
  Builder.start builder (Builder.block builder);
  if not (is_trivial context ty) then begin
    let typed = Builder.local builder (Pointer { target = Value ty; writable = true }) in
    Builder.emit builder (Assign (Builder.at typed, Use (Copy (Builder.at untyped))));
    Builder.emit builder
      (Call
         {
           target =
             Direct { function_ = Instance (Drop ty); signature = Convention.drop_signature ty };
           arguments = [ Copy (Builder.at typed) ];
           result = Discarded;
         })
  end;
  Builder.finish builder (Return None);
  Builder.build builder { parameters = [ untyped ]; result = None; returns = true }

let copy_signature context ty : Lowered.signature =
  Convention.signature
    (Option.to_list (Convention.parameter context.env Read ty))
    (Convention.result context.env ty)

let copy_into context builder ~destination ~source ty =
  if is_trivial context ty then Builder.emit builder (Assign (destination, Use (Copy source)))
  else
    let arguments =
      match Convention.parameter context.env Read ty with
      | Some (Pointer _) -> [ Lowered.Address { place = source; writable = false } ]
      | Some _ -> [ Lowered.Copy source ]
      | None -> []
    in
    Builder.emit builder
      (Call
         {
           target = Direct { function_ = Instance (Copy ty); signature = copy_signature context ty };
           arguments;
           result = Convention.destination (Convention.result context.env ty) destination;
         })

let copied_field context builder ~source (name, member) =
  match member with
  | Memory_layout.Raw _ -> (name, Lowered.Copy source)
  | Typed ty when is_trivial context ty -> (name, Lowered.Copy source)
  | Typed ty ->
      let temporary = Builder.local builder (Value ty) in
      copy_into context builder ~destination:(Builder.at temporary) ~source ty;
      (name, Lowered.Move (Builder.at temporary))

let copy context ty =
  let builder = Builder.create context.env ~key:(Copy ty) in
  let convention = Convention.result context.env ty in
  let result_pointer =
    match convention with
    | Through_pointer pointer -> Some (Builder.local builder ~name:"result" pointer)
    | Returned _ | Nothing -> None
  in
  let parameter = Convention.parameter context.env Read ty in
  let self_local = Option.map (fun ty -> Builder.local builder ~name:"self" ty) parameter in
  let self : Lowered.place =
    match (parameter, self_local) with
    | Some (Pointer _), Some local -> { root = Local local; projections = [ Deref ] }
    | Some _, Some local -> Builder.at local
    | _ -> Builder.at 0
  in
  let result_local =
    match result_pointer with
    | None -> Some (Builder.local builder ~name:"copy" (Value ty))
    | Some _ -> None
  in
  let result : Lowered.place =
    match (result_pointer, result_local) with
    | Some pointer, _ -> { root = Local pointer; projections = [ Deref ] }
    | None, Some local -> Builder.at local
    | None, None -> bug "no place for the copy"
  in
  Builder.start builder (Builder.block builder);
  (match Representation.classify context.env ty with
  | Handle -> bug "a copy of a handle, which is not Copyable"
  | Any ->
      let copied = Builder.local builder (Raw (Pointer Opaque)) in
      Builder.emit builder
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
             result = Returned (Builder.at copied);
           });
      Builder.emit builder
        (Assign
           ( result,
             Build
               {
                 ty;
                 variant = None;
                 fields =
                   [
                     ("value", Copy (Builder.at copied));
                     ("vtable", Copy (Lowered.project self (Field "vtable")));
                   ];
               } ))
  | Shape (Scalar _) -> bug "a copy of the scalar %s, which is trivial" (Ground.to_string ty)
  | Shared _ ->
      Builder.emit builder
        (Call
           {
             target = Intrinsic Shared_retain;
             arguments = [ Copy (Lowered.project self (Field "value")) ];
             result = Discarded;
           });
      Builder.emit builder (Assign (result, Use (Copy self)))
  | Storage element ->
      let layout = Memory_layout.of_type context.env element in
      let unallocated = Builder.block builder
      and allocate = Builder.block builder
      and after = Builder.block builder in
      Builder.branch builder
        (condition builder (Storage.build_is_allocated self))
        ~yes:allocate ~no:unallocated;
      Builder.start builder unallocated;
      Builder.emit builder (Assign (result, Storage.build_empty ty));
      Builder.finish builder (Goto after);
      Builder.start builder allocate;
      let bytes = Builder.local builder (Raw (Integer UInt64)) in
      let buffer = Builder.local builder ~name:"buffer" (Raw (Pointer (Data element))) in
      Builder.emit builder
        (Assign
           ( Builder.at bytes,
             Binary
               (Multiply, Copy (Storage.project_capacity self), Builder.constant_uint64 layout.size)
           ));
      Builder.emit builder
        (Call
           {
             target = Intrinsic Allocate;
             arguments = [ Copy (Builder.at bytes); Builder.constant_uint64 layout.alignment ];
             result = Returned (Builder.at buffer);
           });
      if is_trivial context element then begin
        let used = Builder.local builder (Raw (Integer UInt64)) in
        Builder.emit builder
          (Assign
             ( Builder.at used,
               Binary
                 (Multiply, Copy (Storage.project_length self), Builder.constant_uint64 layout.size)
             ));
        Builder.emit builder
          (Call
             {
               target = Intrinsic Copy_bytes;
               arguments =
                 [
                   Copy (Builder.at buffer);
                   Copy (Storage.project_buffer self);
                   Copy (Builder.at used);
                 ];
               result = Discarded;
             })
      end
      else
        Builder.loop builder
          ~count:(Copy (Storage.project_length self))
          (fun index ->
            copy_into context builder
              ~destination:(Lowered.project (Builder.at buffer) (Index (Copy (Builder.at index))))
              ~source:(Storage.index_element self (Copy (Builder.at index)))
              element);
      Builder.emit builder
        (Assign
           ( result,
             Storage.build_storage ty
               ~buffer:(Copy (Builder.at buffer))
               ~length:(Copy (Storage.project_length self))
               ~capacity:(Copy (Storage.project_capacity self)) ));
      Builder.finish builder (Goto after);
      Builder.start builder after
  | Shape (Record fields) ->
      let fields =
        List.map
          (fun (name, member) ->
            copied_field context builder ~source:(Lowered.project self (Field name)) (name, member))
          fields
      in
      Builder.emit builder (Assign (result, Build { ty; variant = None; fields }))
  | Shape (Array (element, count)) ->
      Builder.loop builder ~count:(Builder.constant_uint64 count) (fun index ->
          copy_into context builder
            ~destination:(Lowered.project result (Index (Copy (Builder.at index))))
            ~source:(Lowered.project self (Index (Copy (Builder.at index))))
            element)
  | Shape (Sum variants) ->
      let after = Builder.block builder in
      let cases =
        List.map
          (fun (variant_shape : Memory_layout.variant_shape) ->
            let block = Builder.block builder in
            Builder.in_block builder block (fun () ->
                let fields =
                  List.map
                    (fun (name, member) ->
                      copied_field context builder
                        ~source:
                          (Lowered.project self
                             (Variant_field { variant = variant_shape.name; field = name }))
                        (name, member))
                    variant_shape.fields
                in
                Builder.emit builder
                  (Assign (result, Build { ty; variant = Some variant_shape.name; fields }));
                Builder.finish builder (Goto after));
            (variant_shape.name, block))
          variants
      in
      Builder.finish builder (Switch_variant { place = self; cases; default = None });
      Builder.start builder after);
  (match result_local with
  | Some local -> Builder.finish builder (Return (Some (Move (Builder.at local))))
  | None -> Builder.finish builder (Return None));
  let parameters = Option.to_list result_pointer @ Option.to_list self_local in
  Builder.build builder
    {
      parameters;
      result =
        (match convention with Returned ty -> Some ty | Nothing | Through_pointer _ -> None);
      returns = true;
    }

let any_copy context ty =
  let builder = Builder.create context.env ~key:(Any_copy ty) in
  let original = Builder.local builder ~name:"value" (Raw (Pointer Opaque)) in
  Builder.start builder (Builder.block builder);
  let copied = box context builder ty in
  if not (Memory_layout.has_zero_size context.env ty) then begin
    let source = Builder.local builder (Pointer { target = Value ty; writable = false }) in
    let destination = Builder.local builder (Pointer { target = Value ty; writable = true }) in
    Builder.emit builder (Assign (Builder.at source, Use (Copy (Builder.at original))));
    Builder.emit builder (Assign (Builder.at destination, Use (Copy (Builder.at copied))));
    copy_into context builder
      ~destination:{ root = Local destination; projections = [ Deref ] }
      ~source:{ root = Local source; projections = [ Deref ] }
      ty
  end;
  Builder.finish builder (Return (Some (Copy (Builder.at copied))));
  Builder.build builder
    { parameters = [ original ]; result = Some (Raw (Pointer Opaque)); returns = true }

module For_testing = struct
  let copy_signature = copy_signature
end
