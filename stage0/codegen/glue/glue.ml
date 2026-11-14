let bug format = Compiler_bug.bug ~stage:"Glue" format

module Types = Map.Make (struct
  type t = Ground.ty

  let compare = Ground.compare
end)

type debug_form = Structure | Text | Sequence

type t = {
  env : Memory_layout.env;
  representation : Ground.ty -> Memory_layout.representation;
  usize : Ground.ty;
  debug_form : Ground.ty -> debug_form;
  mutable trivial_types : bool Types.t;
}

let create env ~representation ~usize ?(debug_form = fun _ -> Structure) () =
  { env; representation; usize; debug_form; trivial_types = Types.empty }

let rec trivial glue ty =
  match Types.find_opt ty glue.trivial_types with
  | Some answer -> answer
  | None ->
      (* A type that contains itself does so through an [indirect] variant
         or storage, so it is not trivial, which is the answer a cycle
         gets. *)
      glue.trivial_types <- Types.add ty false glue.trivial_types;
      (* An [any] value and a cursor always have a drop function, which a
         cursor's shape, made from its method's body, need not be looked at
         to know. *)
      let any = match ty with Ground.Any _ | Cursor _ -> true | _ -> false in
      let member : Memory_layout.member -> bool = function
        | Typed ty -> trivial glue ty
        | Raw _ -> true
      in
      let answer =
        if any then false
        else
          match glue.representation ty with
          | Storage _ | Handle | Shared _ -> false
          | Shape (Scalar _) -> true
          | Shape (Record fields) ->
              List.for_all (fun (_, field_member) -> member field_member) fields
          | Shape (Array (element, _)) -> trivial glue element
          | Shape (Sum variants) ->
              List.for_all
                (fun (variant_shape : Memory_layout.variant_shape) ->
                  (not variant_shape.indirect)
                  && List.for_all
                       (fun (_, field_member) -> member field_member)
                       variant_shape.fields)
                variants
      in
      glue.trivial_types <- Types.add ty answer glue.trivial_types;
      answer

open Emit_c.Builder

let loop glue builder ~count body = loop builder ~index_type:(Value glue.usize) ~count body

(* Writes a test, and gives its result, a [Bool]. *)
let test builder rvalue =
  let result = local builder (Raw Bool) in
  emit builder (Assign (at result, rvalue));
  Lowered.Copy (at result)

(* Writes a test of whether the storage at a place owns a buffer. *)
let owns_buffer builder storage =
  test builder (Binary (Not_equal, Copy (Storage.capacity storage), usize 0))

(* Writes a test of whether the storage at a place has no elements. *)
let is_empty builder storage = test builder (Binary (Equal, Copy (Storage.length storage), usize 0))

let variant_shapes glue ty =
  match glue.representation ty with
  | Shape (Sum variants) -> variants
  | _ -> bug "%s is not a sum type" (Ground.to_string ty)

let droppable glue : Memory_layout.member -> bool = function
  | Typed ty -> not (trivial glue ty)
  | Raw _ -> false

let drop glue ty =
  let builder = create glue.env ~key:(Drop ty) in
  let pointer = local builder ~name:"value" (Pointer { target = Value ty; writable = true }) in
  let value : Lowered.place = { root = Local pointer; projections = [ Deref ] } in
  start builder (block builder);
  (match (ty, glue.representation ty) with
  | Any _, _ ->
      (* The value's own drop, from slot 0 of its table, then its block. *)
      emit builder
        (Call
           {
             target =
               Table_call
                 {
                   table = Copy (value / Field "vtable");
                   value = Copy (value / Field "value");
                   slot = 0;
                   signature =
                     { parameters = [ Raw (Pointer Opaque) ]; result = None; returns = true };
                 };
             arguments = [];
             result = Discarded;
           });
      emit builder
        (Call
           {
             target = Intrinsic Free;
             arguments = [ Copy (value / Field "value") ];
             result = Discarded;
           })
  | _, Handle ->
      emit builder
        (Call
           {
             target = Foreign (Libc.declaration (Memory_layout.target glue.env).system Close);
             arguments = [ Copy (value / Field "descriptor") ];
             result = Discarded;
           })
  | _, Shared inner ->
      (* The last reference drops the value, by a call of its type's drop
         function, and frees the block. *)
      let pointer = Lowered.Copy (value / Field "value") in
      let last = local builder (Raw Bool) in
      emit builder
        (Call
           {
             target = Intrinsic Shared_release;
             arguments = [ pointer ];
             result = Returned (at last);
           });
      when_ builder
        (Copy (at last))
        (fun () ->
          if not (trivial glue inner) then begin
            let typed = local builder (Pointer { target = Value inner; writable = true }) in
            emit builder (Assign (at typed, Use pointer));
            emit builder
              (Call
                 {
                   target =
                     Direct
                       {
                         function_ = Instance (Drop inner);
                         signature = Convention.drop_signature inner;
                       };
                   arguments = [ Copy (at typed) ];
                   result = Discarded;
                 })
          end;
          emit builder
            (Call { target = Intrinsic Shared_free; arguments = [ pointer ]; result = Discarded }))
  | _, Storage element ->
      if not (trivial glue element) then
        loop glue builder
          ~count:(Copy (Storage.length value))
          (fun index -> emit builder (Drop (Storage.at value (Copy (at index)))));
      when_ builder (owns_buffer builder value) (fun () ->
          emit builder
            (Call
               {
                 target = Intrinsic Free;
                 arguments = [ Copy (Storage.buffer value) ];
                 result = Discarded;
               }))
  | _, Shape (Record fields) ->
      List.iter
        (fun (name, member) ->
          if droppable glue member then emit builder (Drop (value / Field name)))
        fields
  | _, Shape (Array (element, count)) ->
      if not (trivial glue element) then
        loop glue builder ~count:(usize count) (fun index ->
            emit builder (Drop (value / Index (Copy (at index)))))
  | _, Shape (Sum variants) ->
      let after = block builder in
      let cases =
        List.filter_map
          (fun (variant_shape : Memory_layout.variant_shape) ->
            if
              variant_shape.indirect
              || List.exists
                   (fun (_, field_member) -> droppable glue field_member)
                   variant_shape.fields
            then begin
              let block = block builder in
              in_block builder block (fun () ->
                  List.iter
                    (fun (field, member) ->
                      if droppable glue member then
                        emit builder
                          (Drop (value / Variant_field { variant = variant_shape.name; field })))
                    variant_shape.fields;
                  if variant_shape.indirect then
                    emit builder (Free_block { place = value; variant = variant_shape.name });
                  finish builder (Goto after));
              Some (variant_shape.name, block)
            end
            else None)
          variants
      in
      finish builder (Switch_variant { place = value; cases; default = Some after });
      start builder after
  | _, Shape (Scalar _) -> ());
  finish builder (Return None);
  build builder ~parameters:[ pointer ] ~result:None;
  built builder

(* The drop in slot 0 of an [any] table, which takes the value's pointer
   untyped, as the slot is called. It calls the type's drop function. *)
let any_drop glue ty =
  let builder = create glue.env ~key:(Any_drop ty) in
  let untyped = local builder ~name:"value" (Raw (Pointer Opaque)) in
  start builder (block builder);
  if not (trivial glue ty) then begin
    let typed = local builder (Pointer { target = Value ty; writable = true }) in
    emit builder (Assign (at typed, Use (Copy (at untyped))));
    emit builder
      (Call
         {
           target =
             Direct { function_ = Instance (Drop ty); signature = Convention.drop_signature ty };
           arguments = [ Copy (at typed) ];
           result = Discarded;
         })
  end;
  finish builder (Return None);
  build builder ~parameters:[ untyped ] ~result:None;
  built builder

let copy_signature glue ty : Lowered.signature =
  Convention.signature
    (Option.to_list (Convention.parameter glue.env Read ty))
    (Convention.result glue.env ty)

let copy_into glue builder ~destination ~source ty =
  if trivial glue ty then emit builder (Assign (destination, Use (Copy source)))
  else
    let signature = copy_signature glue ty in
    let argument =
      match Convention.parameter glue.env Read ty with
      | Some (Pointer _) -> [ Lowered.Address { place = source; writable = false } ]
      | Some _ -> [ Lowered.Copy source ]
      | None -> []
    in
    let target = Lowered.Direct { function_ = Instance (Copy ty); signature } in
    emit builder
      (Call
         {
           target;
           arguments = argument;
           result = Convention.(destination (result glue.env ty)) destination;
         })

(* The operand for a copy of a field, through a temporary when the field's
   type is not trivial. *)
let copied_field glue builder ~source (name, member) =
  match member with
  | Memory_layout.Raw _ -> (name, Lowered.Copy source)
  | Typed ty when trivial glue ty -> (name, Lowered.Copy source)
  | Typed ty ->
      let temporary = local builder (Value ty) in
      copy_into glue builder ~destination:(at temporary) ~source ty;
      (name, Lowered.Move (at temporary))

let copy glue ty =
  let builder = create glue.env ~key:(Copy ty) in
  let convention = Convention.result glue.env ty in
  let result_pointer =
    match convention with
    | Through_pointer pointer -> Some (local builder ~name:"result" pointer)
    | Returned _ | Nothing -> None
  in
  let parameter = Convention.parameter glue.env Read ty in
  let self_local = Option.map (fun ty -> local builder ~name:"self" ty) parameter in
  let self : Lowered.place =
    match (parameter, self_local) with
    | Some (Pointer _), Some local -> { root = Local local; projections = [ Deref ] }
    | Some _, Some local -> at local
    | _ -> at 0
  in
  let result_local =
    match result_pointer with
    | None -> Some (local builder ~name:"copy" (Value ty))
    | Some _ -> None
  in
  let result : Lowered.place =
    match (result_pointer, result_local) with
    | Some pointer, _ -> { root = Local pointer; projections = [ Deref ] }
    | None, Some local -> at local
    | None, None -> bug "no place for the copy"
  in
  start builder (block builder);
  (if trivial glue ty then emit builder (Assign (result, Use (Copy self)))
   else
     match glue.representation ty with
     | Handle -> bug "a copy of a handle, which is not Copyable"
     | Shared _ ->
         (* A copy is another reference to the same block. *)
         emit builder
           (Call
              {
                target = Intrinsic Shared_retain;
                arguments = [ Copy (self / Field "value") ];
                result = Discarded;
              });
         emit builder (Assign (result, Use (Copy self)))
     | Storage element ->
         (* A storage that owns no buffer, empty or static, is shared. One
            that owns a buffer is never shared, or two would free it: with
            no elements its copy is empty, and otherwise its copy gets a
            buffer of exactly its length. *)
         let layout = Memory_layout.of_type glue.env element in
         let share = block builder and owning = block builder and hollow = block builder in
         let allocate = block builder and after = block builder in
         let owns = owns_buffer builder self in
         branch builder owns ~yes:owning ~no:share;
         start builder share;
         emit builder (Assign (result, Use (Copy self)));
         finish builder (Goto after);
         start builder owning;
         let empty = is_empty builder self in
         branch builder empty ~yes:hollow ~no:allocate;
         start builder hollow;
         emit builder (Assign (result, Storage.empty ty));
         finish builder (Goto after);
         start builder allocate;
         let bytes = local builder (Value glue.usize) in
         let buffer = local builder ~name:"buffer" (Raw (Pointer (Data element))) in
         emit builder
           (Assign (at bytes, Binary (Multiply, Copy (Storage.length self), usize layout.size)));
         emit builder
           (Call
              {
                target = Intrinsic Allocate;
                arguments = [ Copy (at bytes); usize layout.alignment ];
                result = Returned (at buffer);
              });
         if trivial glue element then
           emit builder
             (Call
                {
                  target = Intrinsic Copy_bytes;
                  arguments = [ Copy (at buffer); Copy (Storage.buffer self); Copy (at bytes) ];
                  result = Discarded;
                })
         else
           loop glue builder
             ~count:(Copy (Storage.length self))
             (fun index ->
               copy_into glue builder
                 ~destination:(at buffer / Index (Copy (at index)))
                 ~source:(Storage.at self (Copy (at index)))
                 element);
         emit builder
           (Assign
              ( result,
                Storage.owning ty
                  ~buffer:(Copy (at buffer))
                  ~length:(Copy (Storage.length self))
                  ~capacity:(Copy (Storage.length self)) ));
         finish builder (Goto after);
         start builder after
     | Shape (Record fields) ->
         let fields =
           List.map
             (fun (name, member) ->
               copied_field glue builder ~source:(self / Field name) (name, member))
             fields
         in
         emit builder (Assign (result, Build { ty; variant = None; fields }))
     | Shape (Array (element, count)) ->
         loop glue builder ~count:(usize count) (fun index ->
             copy_into glue builder
               ~destination:(result / Index (Copy (at index)))
               ~source:(self / Index (Copy (at index)))
               element)
     | Shape (Sum _) ->
         let after = block builder in
         let cases =
           List.map
             (fun (variant_shape : Memory_layout.variant_shape) ->
               let block = block builder in
               in_block builder block (fun () ->
                   let fields =
                     List.map
                       (fun (name, member) ->
                         copied_field glue builder
                           ~source:
                             (self / Variant_field { variant = variant_shape.name; field = name })
                           (name, member))
                       variant_shape.fields
                   in
                   emit builder
                     (Assign (result, Build { ty; variant = Some variant_shape.name; fields }));
                   finish builder (Goto after));
               (variant_shape.name, block))
             (variant_shapes glue ty)
         in
         finish builder (Switch_variant { place = self; cases; default = None });
         start builder after
     | Shape (Scalar _) -> emit builder (Assign (result, Use (Copy self))));
  (match result_local with
  | Some local -> finish builder (Return (Some (Move (at local))))
  | None -> finish builder (Return None));
  let parameters = Option.to_list result_pointer @ Option.to_list self_local in
  build builder ~parameters
    ~result:(match convention with Returned ty -> Some ty | Nothing | Through_pointer _ -> None);
  built builder

let builtin builtin : Ground.ty = Named { path = Intrinsic.builtin_path builtin; arguments = [] }
let output_ty = Storage.of_elements (builtin UInt8)
let bytes_ty = Storage.view_of_elements (builtin UInt8)

let output_parameter glue =
  match Convention.parameter glue.env Mut output_ty with
  | Some parameter -> parameter
  | None -> bug "storage of no size"

let debug_signature glue ty : Lowered.signature =
  {
    parameters =
      (if Memory_layout.has_zero_size glue.env ty then []
       else [ Lowered.Pointer { target = Value ty; writable = false } ])
      @ [ output_parameter glue ];
    result = None;
    returns = true;
  }

(* A call of one of the standard library's functions that append to the
   output, each in [standard::writing]: it takes the output, and a value of
   [ty] to write, which is at [place]. *)
let write glue builder ~output name ty (place : Lowered.place) =
  let key = Instance.Code { path = Path.standard [ "writing" ] name; type_arguments = [] } in
  let parameter, written =
    match Convention.parameter glue.env Read ty with
    | Some (Pointer _ as parameter) -> (parameter, Lowered.Address { place; writable = false })
    | Some parameter -> (parameter, Copy place)
    | None -> bug "%s is written, and has no size" (Ground.to_string ty)
  in
  emit builder
    (Call
       {
         target =
           Direct
             {
               function_ = Instance key;
               signature = Convention.signature [ output_parameter glue; parameter ] Nothing;
             };
         arguments = [ output; written ];
         result = Discarded;
       })

(* A view of bytes, in a local. *)
let bytes builder ~elements ~length =
  let view = local builder (Value bytes_ty) in
  emit builder (Assign (at view, Storage.view bytes_ty ~elements ~length));
  at view

let text glue builder ~output value =
  if value <> "" then
    write glue builder ~output "append" bytes_ty
      (bytes builder ~elements:(Constant (Bytes value)) ~length:(usize (String.length value)))

let debug_call glue builder ~output ty (place : Lowered.place) =
  let arguments =
    if Memory_layout.has_zero_size glue.env ty then []
    else [ Lowered.Address { place; writable = false } ]
  in
  emit builder
    (Call
       {
         target = Direct { function_ = Instance (Debug ty); signature = debug_signature glue ty };
         arguments = arguments @ [ output ];
         result = Discarded;
       })

let scalar_debug glue builder ~output (scalar : Memory_layout.scalar) (place : Lowered.place) =
  let widened name wide =
    let value = local builder (Value (builtin wide)) in
    emit builder
      (Assign
         ( at value,
           Convert (Copy place, Integer (match wide with Intrinsic.Int64 -> Int64 | _ -> UInt64)) ));
    write glue builder ~output name (builtin wide) (at value)
  in
  match scalar with
  | Integer (Int8 | Int16 | Int32 | Int64 | ISize) -> widened "signed" Int64
  | Integer (UInt8 | UInt16 | UInt32 | UInt64 | USize) -> widened "unsigned" UInt64
  | Float32 -> write glue builder ~output "float32" (builtin Float32) place
  | Float64 -> write glue builder ~output "float64" (builtin Float64) place
  | Bool -> write glue builder ~output "boolean" (builtin Bool) place
  | Character -> write glue builder ~output "quoted_character" (builtin Character) place
  | Pointer _ | Nullable_pointer _ -> text glue builder ~output "pointer"

let debug glue ty =
  let builder = create glue.env ~key:(Debug ty) in
  let parameter =
    if Memory_layout.has_zero_size glue.env ty then None
    else Some (local builder ~name:"value" (Pointer { target = Value ty; writable = false }))
  in
  let value : Lowered.place =
    match parameter with
    | Some parameter_local -> { root = Local parameter_local; projections = [ Deref ] }
    | None -> at 0
  in
  let out = local builder ~name:"output" (output_parameter glue) in
  let output = Lowered.Copy (at out) in
  let text = text glue builder ~output in
  let debug_call = debug_call glue builder ~output in
  start builder (block builder);
  let rec list_of element ~element_at ~count =
    text "[";
    loop glue builder ~count (fun index ->
        let later = local builder (Raw Bool) in
        emit builder (Assign (at later, Binary (Not_equal, Copy (at index), usize 0)));
        when_ builder (Copy (at later)) (fun () -> text ", ");
        debug_call element (element_at (Lowered.Copy (at index))));
    text "]"
  and storage_or_view field_ty (place : Lowered.place) ~as_text =
    let element, buffer, count =
      match (Storage.elements_of field_ty, Storage.viewed field_ty) with
      | Some element, _ -> (element, Storage.buffer place, Storage.length place)
      | None, Some element -> (element, Storage.view_elements place, Storage.view_length place)
      | None, None -> bug "%s is not storage or a view" (Ground.to_string field_ty)
    in
    if as_text then
      write glue builder ~output "quoted_text" bytes_ty
        (bytes builder ~elements:(Copy buffer) ~length:(Copy count))
    else list_of element ~element_at:(fun index -> buffer / Index index) ~count:(Copy count)
  and fields_debug name (fields : (string * Memory_layout.member) list) field_place =
    text name;
    match fields with
    | [] -> ()
    | [ (field, Typed field_ty) ] ->
        text "(";
        debug_call field_ty (field_place field);
        text ")"
    | fields ->
        text "(";
        List.iteri
          (fun index (field, member) ->
            match member with
            | Memory_layout.Typed field_ty ->
                text ((if index > 0 then ", " else "") ^ field ^ ": ");
                debug_call field_ty (field_place field)
            | Raw _ -> ())
          fields;
        text ")"
  in
  (match (glue.debug_form ty, glue.representation ty) with
  | (Text | Sequence), Shape (Record [ (field, Typed field_ty) ]) ->
      storage_or_view field_ty (value / Field field) ~as_text:(glue.debug_form ty = Text)
  | _, Handle -> text "Handle"
  | _, Shared _ -> text "Shared"
  | _, Storage element ->
      list_of element ~element_at:(Storage.at value) ~count:(Copy (Storage.length value))
  | _, Shape shape -> (
      match (ty, shape) with
      | Never, _ -> ()
      | Function _, _ -> text "fn"
      | Any _, _ -> text "any"
      | Cursor _, _ -> text "cursor"
      | Lent _, _ ->
          bug "debug glue for %s, which a lent value is copied into first" (Ground.to_string ty)
      | _, Scalar scalar -> scalar_debug glue builder ~output scalar value
      | Named { path; _ }, Record [] ->
          text (if Ground.path_name path = "Unit" then "Unit" else Ground.path_name path ^ "()")
      | Named { path; _ }, Record fields ->
          fields_debug (Ground.path_name path) fields (fun field -> value / Field field)
      | _, Array (element, count) ->
          list_of element ~element_at:(fun index -> value / Index index) ~count:(usize count)
      | _, Sum variants ->
          let after = block builder in
          let cases =
            List.map
              (fun (variant_shape : Memory_layout.variant_shape) ->
                let case = block builder in
                in_block builder case (fun () ->
                    fields_debug variant_shape.name variant_shape.fields (fun field ->
                        value / Variant_field { variant = variant_shape.name; field });
                    finish builder (Goto after));
                (variant_shape.name, case))
              variants
          in
          finish builder (Switch_variant { place = value; cases; default = None });
          start builder after));
  finish builder (Return None);
  build builder ~parameters:(Option.to_list parameter @ [ out ]) ~result:None;
  built builder

(* A value's binary form, which code run while compiling writes its result
   in and the compiler reads back as static data: a scalar as its bytes, a
   record's fields in order, a sum's variant index as a [UInt32] and then
   its fields, an array's elements, and storage's length as a [USize] and
   then its elements. A value of zero size writes nothing. Each part of
   another type is written by that type's own function, so a recursive type
   needs nothing more. *)
let encode_signature glue ty = debug_signature glue ty

let encode_call glue builder ~output ty (place : Lowered.place) =
  if not (Memory_layout.has_zero_size glue.env ty) then
    emit builder
      (Call
         {
           target =
             Direct { function_ = Instance (Encode ty); signature = encode_signature glue ty };
           arguments = [ Lowered.Address { place; writable = false }; output ];
           result = Discarded;
         })

let encode glue ty =
  let builder = create glue.env ~key:(Encode ty) in
  let parameter =
    if Memory_layout.has_zero_size glue.env ty then None
    else Some (local builder ~name:"value" (Pointer { target = Value ty; writable = false }))
  in
  let value : Lowered.place =
    match parameter with
    | Some parameter_local -> { root = Local parameter_local; projections = [ Deref ] }
    | None -> at 0
  in
  let out = local builder ~name:"output" (output_parameter glue) in
  let output = Lowered.Copy (at out) in
  let encode_call = encode_call glue builder ~output in
  start builder (block builder);
  (* The value's own bytes, read as bytes whatever it is. *)
  let bytes (place : Lowered.place) size =
    let first = local builder (Raw (Pointer (Data (builtin UInt8)))) in
    emit builder
      (Assign
         (at first, Convert (Address { place; writable = false }, Pointer (Data (builtin UInt8)))));
    write glue builder ~output "append" bytes_ty
      (bytes builder ~elements:(Copy (at first)) ~length:(usize size))
  in
  let fields place variant (fields : (string * Memory_layout.member) list) =
    List.iter
      (fun (name, member) ->
        match member with
        | Memory_layout.Typed field_ty ->
            encode_call field_ty
              (match variant with
              | None -> place / Field name
              | Some variant -> place / Variant_field { variant; field = name })
        | Raw _ -> bug "a raw field in a value written out")
      fields
  in
  (if parameter <> None then
     match glue.representation ty with
     | Handle -> bug "a handle cannot be computed while compiling"
     | Shared _ -> bug "a shared value cannot be computed while compiling"
     | Storage element ->
         bytes (Storage.length value) (Memory_layout.of_type glue.env glue.usize).size;
         loop glue builder
           ~count:(Copy (Storage.length value))
           (fun index -> encode_call element (Storage.at value (Copy (at index))))
     | Shape (Scalar _) -> bytes value (Memory_layout.of_type glue.env ty).size
     | Shape (Record members) -> fields value None members
     | Shape (Array (element, count)) ->
         loop glue builder ~count:(usize count) (fun index ->
             encode_call element (value / Index (Copy (at index))))
     | Shape (Sum variants) ->
         let after = block builder in
         let cases =
           List.mapi
             (fun variant_index (variant_shape : Memory_layout.variant_shape) ->
               let case = block builder in
               in_block builder case (fun () ->
                   let index = local builder (Raw (Integer UInt32)) in
                   emit builder
                     (Assign (at index, Use (Constant (Integer (UInt32, Z.of_int variant_index)))));
                   bytes (at index) 4;
                   fields value (Some variant_shape.name) variant_shape.fields;
                   finish builder (Goto after));
               (variant_shape.name, case))
             variants
         in
         finish builder (Switch_variant { place = value; cases; default = None });
         start builder after);
  finish builder (Return None);
  build builder ~parameters:(Option.to_list parameter @ [ out ]) ~result:None;
  built builder

module For_testing = struct
  let copy_signature = copy_signature
end
