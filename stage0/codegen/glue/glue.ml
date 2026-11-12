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

let rec trivial t ty =
  match Types.find_opt ty t.trivial_types with
  | Some answer -> answer
  | None ->
      (* A type that contains itself does so through an [indirect] variant
         or storage, so it is not trivial, which is the answer a cycle
         gets. *)
      t.trivial_types <- Types.add ty false t.trivial_types;
      (* An [any] value and a cursor always have a drop function, which a
         cursor's shape, made from its method's body, need not be looked at
         to know. *)
      let any = match ty with Ground.Any _ | Cursor _ -> true | _ -> false in
      let member : Memory_layout.member -> bool = function
        | Typed ty -> trivial t ty
        | Raw _ -> true
      in
      let answer =
        if any then false
        else
          match t.representation ty with
          | Storage _ | Handle | Shared _ -> false
          | Shape (Scalar _) -> true
          | Shape (Record fields) -> List.for_all (fun (_, m) -> member m) fields
          | Shape (Array (element, _)) -> trivial t element
          | Shape (Sum variants) ->
              List.for_all
                (fun (v : Memory_layout.variant_shape) ->
                  (not v.indirect) && List.for_all (fun (_, m) -> member m) v.fields)
                variants
      in
      t.trivial_types <- Types.add ty answer t.trivial_types;
      answer

open Lir_builder

let loop t b ~count body = loop b ~index_type:(Value t.usize) ~count body
let instance key main : Lir.t = { key; main; nested = [||] }

let variant_shapes t ty =
  match t.representation ty with
  | Shape (Sum variants) -> variants
  | _ -> bug "%s is not a sum type" (Ground.to_string ty)

(* Drop *)

let droppable t : Memory_layout.member -> bool = function
  | Typed ty -> not (trivial t ty)
  | Raw _ -> false

let drop t ty =
  let b = create () in
  let pointer = local b ~name:"value" (Pointer { target = Value ty; writable = true }) in
  let value : Lir.place = { root = Local pointer; projections = [ Deref ] } in
  start b (block b);
  (match (ty, t.representation ty) with
  | Any _, _ ->
      (* The value's own drop, from slot 0 of its table, then its block. *)
      emit b
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
      emit b
        (Call
           {
             target = Intrinsic Free;
             arguments = [ Copy (value / Field "value") ];
             result = Discarded;
           })
  | _, Handle ->
      emit b
        (Call
           {
             target = Foreign (Libc.declaration (Memory_layout.target t.env).system Close);
             arguments = [ Copy (value / Field "descriptor") ];
             result = Discarded;
           })
  | _, Shared inner ->
      (* The last reference drops the value and frees the block. The value
         is dropped by a call of its type's drop function: drop elaboration
         would remove a [Drop] of a place behind a local pointer. *)
      let pointer = Lir.Copy (value / Field "value") in
      let last = local b (Raw Bool) in
      emit b
        (Call
           {
             target = Intrinsic Shared_release;
             arguments = [ pointer ];
             result = Returned (at last);
           });
      when_ b
        (Copy (at last))
        (fun () ->
          if not (trivial t inner) then begin
            let typed = local b (Pointer { target = Value inner; writable = true }) in
            emit b (Assign (at typed, Use pointer));
            emit b
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
          emit b
            (Call { target = Intrinsic Shared_free; arguments = [ pointer ]; result = Discarded }))
  | _, Storage element ->
      if not (trivial t element) then
        loop t b
          ~count:(Copy (Storage.length value))
          (fun index -> emit b (Drop (Storage.at value (Copy (at index)))));
      when_ b (Storage.owns_buffer b value) (fun () ->
          emit b
            (Call
               {
                 target = Intrinsic Free;
                 arguments = [ Copy (Storage.buffer value) ];
                 result = Discarded;
               }))
  | _, Shape (Record fields) ->
      List.iter
        (fun (name, member) -> if droppable t member then emit b (Drop (value / Field name)))
        fields
  | _, Shape (Array (element, count)) ->
      if not (trivial t element) then
        loop t b ~count:(usize count) (fun index -> emit b (Drop (value / Index (Copy (at index)))))
  | _, Shape (Sum variants) ->
      let after = block b in
      let cases =
        List.filter_map
          (fun (v : Memory_layout.variant_shape) ->
            if v.indirect || List.exists (fun (_, m) -> droppable t m) v.fields then begin
              let block = block b in
              aside b block (fun () ->
                  List.iter
                    (fun (field, member) ->
                      if droppable t member then
                        emit b (Drop (value / Variant_field { variant = v.name; field })))
                    v.fields;
                  if v.indirect then emit b (Free_block { place = value; variant = v.name });
                  finish b (Goto after));
              Some (v.name, block)
            end
            else None)
          variants
      in
      finish b (Switch_variant { place = value; cases; default = Some after });
      start b after
  | _, Shape (Scalar _) -> ());
  finish b (Return None);
  instance (Drop ty) (build b ~parameters:[ pointer ] ~result:None)

(* The drop in slot 0 of an [any] table, which takes the value's pointer
   untyped, as the slot is called. It calls the type's drop function. A
   [Drop] statement would be removed: drop elaboration treats a place
   behind a pointer that is not a parameter as uninitialized. *)
let any_drop t ty =
  let b = create () in
  let untyped = local b ~name:"value" (Raw (Pointer Opaque)) in
  start b (block b);
  if not (trivial t ty) then begin
    let typed = local b (Pointer { target = Value ty; writable = true }) in
    emit b (Assign (at typed, Use (Copy (at untyped))));
    emit b
      (Call
         {
           target =
             Direct { function_ = Instance (Drop ty); signature = Convention.drop_signature ty };
           arguments = [ Copy (at typed) ];
           result = Discarded;
         })
  end;
  finish b (Return None);
  instance (Any_drop ty) (build b ~parameters:[ untyped ] ~result:None)

(* Copy *)

let copy_signature t ty : Lir.signature =
  Convention.signature
    (Option.to_list (Convention.parameter t.env Read ty))
    (Convention.result t.env ty)

(* Copies [source] into [destination], both of type [ty]. *)
let copy_into t b ~destination ~source ty =
  if trivial t ty then emit b (Assign (destination, Use (Copy source)))
  else
    let signature = copy_signature t ty in
    let argument =
      match Convention.parameter t.env Read ty with
      | Some (Pointer _) -> [ Lir.Address { place = source; writable = false } ]
      | Some _ -> [ Lir.Copy source ]
      | None -> []
    in
    let target = Lir.Direct { function_ = Instance (Copy ty); signature } in
    emit b
      (Call
         {
           target;
           arguments = argument;
           result = Convention.(destination (result t.env ty)) destination;
         })

(* The operand for a copy of a field, through a temporary when the field's
   type is not trivial. *)
let copied_field t b ~source (name, member) =
  match member with
  | Memory_layout.Raw _ -> (name, Lir.Copy source)
  | Typed ty when trivial t ty -> (name, Lir.Copy source)
  | Typed ty ->
      let temporary = local b (Value ty) in
      copy_into t b ~destination:(at temporary) ~source ty;
      (name, Lir.Move (at temporary))

let copy t ty =
  let b = create () in
  let convention = Convention.result t.env ty in
  let result_pointer =
    match convention with
    | Through_pointer pointer -> Some (local b ~name:"result" pointer)
    | Returned _ | Nothing -> None
  in
  let parameter = Convention.parameter t.env Read ty in
  let self_local = Option.map (fun ty -> local b ~name:"self" ~borrowed:true ty) parameter in
  let self : Lir.place =
    match (parameter, self_local) with
    | Some (Pointer _), Some local -> { root = Local local; projections = [ Deref ] }
    | Some _, Some local -> at local
    | _ -> at 0
  in
  let result_local =
    match result_pointer with None -> Some (local b ~name:"copy" (Value ty)) | Some _ -> None
  in
  let result : Lir.place =
    match (result_pointer, result_local) with
    | Some pointer, _ -> { root = Local pointer; projections = [ Deref ] }
    | None, Some local -> at local
    | None, None -> bug "no place for the copy"
  in
  start b (block b);
  (if trivial t ty then emit b (Assign (result, Use (Copy self)))
   else
     match t.representation ty with
     | Handle -> bug "a copy of a handle, which is not Copyable"
     | Shared _ ->
         (* A copy is another reference to the same block. *)
         emit b
           (Call
              {
                target = Intrinsic Shared_retain;
                arguments = [ Copy (self / Field "value") ];
                result = Discarded;
              });
         emit b (Assign (result, Use (Copy self)))
     | Storage element ->
         (* A storage that owns no buffer, empty or static, is shared. One
            that owns a buffer is never shared, or two would free it: with
            no elements its copy is empty, and otherwise its copy gets a
            buffer of exactly its length. *)
         let layout = Memory_layout.of_type t.env element in
         let share = block b and owning = block b and hollow = block b in
         let allocate = block b and after = block b in
         let owns = Storage.owns_buffer b self in
         branch b owns ~yes:owning ~no:share;
         start b share;
         emit b (Assign (result, Use (Copy self)));
         finish b (Goto after);
         start b owning;
         let empty = Storage.is_empty b self in
         branch b empty ~yes:hollow ~no:allocate;
         start b hollow;
         emit b (Assign (result, Storage.empty ty));
         finish b (Goto after);
         start b allocate;
         let bytes = local b (Value t.usize) in
         let buffer = local b ~name:"buffer" (Raw (Pointer (Data element))) in
         emit b
           (Assign (at bytes, Binary (Multiply, Copy (Storage.length self), usize layout.size)));
         emit b
           (Call
              {
                target = Intrinsic Allocate;
                arguments = [ Copy (at bytes); usize layout.alignment ];
                result = Returned (at buffer);
              });
         if trivial t element then
           emit b
             (Call
                {
                  target = Intrinsic Copy_bytes;
                  arguments = [ Copy (at buffer); Copy (Storage.buffer self); Copy (at bytes) ];
                  result = Discarded;
                })
         else
           loop t b
             ~count:(Copy (Storage.length self))
             (fun index ->
               copy_into t b
                 ~destination:(at buffer / Index (Copy (at index)))
                 ~source:(Storage.at self (Copy (at index)))
                 element);
         emit b
           (Assign
              ( result,
                Storage.owning ty
                  ~buffer:(Copy (at buffer))
                  ~length:(Copy (Storage.length self))
                  ~capacity:(Copy (Storage.length self)) ));
         finish b (Goto after);
         start b after
     | Shape (Record fields) ->
         let fields =
           List.map
             (fun (name, member) -> copied_field t b ~source:(self / Field name) (name, member))
             fields
         in
         emit b (Assign (result, Build { ty; variant = None; fields }))
     | Shape (Array (element, count)) ->
         loop t b ~count:(usize count) (fun index ->
             copy_into t b
               ~destination:(result / Index (Copy (at index)))
               ~source:(self / Index (Copy (at index)))
               element)
     | Shape (Sum _) ->
         let after = block b in
         let cases =
           List.map
             (fun (v : Memory_layout.variant_shape) ->
               let block = block b in
               aside b block (fun () ->
                   let fields =
                     List.map
                       (fun (name, member) ->
                         copied_field t b
                           ~source:(self / Variant_field { variant = v.name; field = name })
                           (name, member))
                       v.fields
                   in
                   emit b (Assign (result, Build { ty; variant = Some v.name; fields }));
                   finish b (Goto after));
               (v.name, block))
             (variant_shapes t ty)
         in
         finish b (Switch_variant { place = self; cases; default = None });
         start b after
     | Shape (Scalar _) -> emit b (Assign (result, Use (Copy self))));
  (match result_local with
  | Some local -> finish b (Return (Some (Move (at local))))
  | None -> finish b (Return None));
  let parameters = Option.to_list result_pointer @ Option.to_list self_local in
  instance (Copy ty)
    (build ?written_result:result_pointer b ~parameters
       ~result:
         (match convention with Returned ty -> Some ty | Nothing | Through_pointer _ -> None))

(* Debug output *)

(* What a debug or an encode function appends to: storage of bytes, which
   its caller owns and passes to be changed. *)
let builtin builtin : Ground.ty = Named { path = Intrinsic.builtin_path builtin; arguments = [] }
let output_ty = Storage.of_elements (builtin UInt8)
let bytes_ty = Storage.view_of_elements (builtin UInt8)

let output_parameter t =
  match Convention.parameter t.env Mut output_ty with
  | Some parameter -> parameter
  | None -> bug "storage of no size"

let debug_signature t ty : Lir.signature =
  {
    parameters =
      (if Memory_layout.has_zero_size t.env ty then []
       else [ Lir.Pointer { target = Value ty; writable = false } ])
      @ [ output_parameter t ];
    result = None;
    returns = true;
  }

(* A call of one of the standard library's functions that append to the
   output, each in [standard::writing]: it takes the output, and a value of
   [ty] to write, which is at [place]. *)
let write t b ~output name ty (place : Lir.place) =
  let key = Instance.Code { path = Path.standard [ "writing" ] name; type_arguments = [] } in
  let parameter, written =
    match Convention.parameter t.env Read ty with
    | Some (Pointer _ as parameter) -> (parameter, Lir.Address { place; writable = false })
    | Some parameter -> (parameter, Copy place)
    | None -> bug "%s is written, and has no size" (Ground.to_string ty)
  in
  emit b
    (Call
       {
         target =
           Direct
             {
               function_ = Instance key;
               signature = Convention.signature [ output_parameter t; parameter ] Nothing;
             };
         arguments = [ output; written ];
         result = Discarded;
       })

(* A view of bytes, in a local. *)
let bytes b ~elements ~length =
  let view = local b (Value bytes_ty) in
  emit b (Assign (at view, Storage.view bytes_ty ~elements ~length));
  at view

let text t b ~output value =
  if value <> "" then
    write t b ~output "append" bytes_ty
      (bytes b ~elements:(Constant (Bytes value)) ~length:(usize (String.length value)))

let debug_call t b ~output ty (place : Lir.place) =
  let arguments =
    if Memory_layout.has_zero_size t.env ty then [] else [ Lir.Address { place; writable = false } ]
  in
  emit b
    (Call
       {
         target = Direct { function_ = Instance (Debug ty); signature = debug_signature t ty };
         arguments = arguments @ [ output ];
         result = Discarded;
       })

let scalar_debug t b ~output (scalar : Memory_layout.scalar) (place : Lir.place) =
  let widened name wide =
    let value = local b (Value (builtin wide)) in
    emit b
      (Assign
         ( at value,
           Convert (Copy place, Integer (match wide with Intrinsic.Int64 -> Int64 | _ -> UInt64)) ));
    write t b ~output name (builtin wide) (at value)
  in
  match scalar with
  | Integer (Int8 | Int16 | Int32 | Int64 | ISize) -> widened "signed" Int64
  | Integer (UInt8 | UInt16 | UInt32 | UInt64 | USize) -> widened "unsigned" UInt64
  | Float32 -> write t b ~output "float32" (builtin Float32) place
  | Float64 -> write t b ~output "float64" (builtin Float64) place
  | Bool -> write t b ~output "truth" (builtin Bool) place
  | Character -> write t b ~output "quoted_character" (builtin Character) place
  | Pointer _ | Nullable_pointer _ -> text t b ~output "pointer"

let debug t ty =
  let b = create () in
  let parameter =
    if Memory_layout.has_zero_size t.env ty then None
    else Some (local b ~name:"value" (Pointer { target = Value ty; writable = false }))
  in
  let value : Lir.place =
    match parameter with Some p -> { root = Local p; projections = [ Deref ] } | None -> at 0
  in
  let out = local b ~name:"output" (output_parameter t) in
  let output = Lir.Copy (at out) in
  let text = text t b ~output in
  let debug_call = debug_call t b ~output in
  start b (block b);
  let rec list_of element ~element_at ~count =
    text "[";
    loop t b ~count (fun index ->
        let later = local b (Raw Bool) in
        emit b (Assign (at later, Binary (Not_equal, Copy (at index), usize 0)));
        when_ b (Copy (at later)) (fun () -> text ", ");
        debug_call element (element_at (Lir.Copy (at index))));
    text "]"
  and storage_or_view field_ty (place : Lir.place) ~as_text =
    let element, buffer, count =
      match (Storage.elements_of field_ty, Storage.viewed field_ty) with
      | Some element, _ -> (element, Storage.buffer place, Storage.length place)
      | None, Some element -> (element, Storage.view_elements place, Storage.view_length place)
      | None, None -> bug "%s is not storage or a view" (Ground.to_string field_ty)
    in
    if as_text then
      write t b ~output "quoted_text" bytes_ty
        (bytes b ~elements:(Copy buffer) ~length:(Copy count))
    else list_of element ~element_at:(fun i -> buffer / Index i) ~count:(Copy count)
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
          (fun i (field, member) ->
            match member with
            | Memory_layout.Typed field_ty ->
                text ((if i > 0 then ", " else "") ^ field ^ ": ");
                debug_call field_ty (field_place field)
            | Raw _ -> ())
          fields;
        text ")"
  in
  (match (t.debug_form ty, t.representation ty) with
  | (Text | Sequence), Shape (Record [ (field, Typed field_ty) ]) ->
      storage_or_view field_ty (value / Field field) ~as_text:(t.debug_form ty = Text)
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
      | _, Scalar scalar -> scalar_debug t b ~output scalar value
      | Named { path; _ }, Record [] ->
          text (if Ground.path_name path = "Unit" then "Unit" else Ground.path_name path ^ "()")
      | Named { path; _ }, Record fields ->
          fields_debug (Ground.path_name path) fields (fun field -> value / Field field)
      | _, Array (element, count) ->
          list_of element ~element_at:(fun i -> value / Index i) ~count:(usize count)
      | _, Sum variants ->
          let after = block b in
          let cases =
            List.map
              (fun (v : Memory_layout.variant_shape) ->
                let case = block b in
                aside b case (fun () ->
                    fields_debug v.name v.fields (fun field ->
                        value / Variant_field { variant = v.name; field });
                    finish b (Goto after));
                (v.name, case))
              variants
          in
          finish b (Switch_variant { place = value; cases; default = None });
          start b after));
  finish b (Return None);
  instance (Debug ty) (build b ~parameters:(Option.to_list parameter @ [ out ]) ~result:None)

(* Encoding *)

(* A value's binary form, which code run while compiling writes its result
   in and the compiler reads back as static data: a scalar as its bytes, a
   record's fields in order, a sum's variant index as a [UInt32] and then
   its fields, an array's elements, and storage's length as a [USize] and
   then its elements. A value of zero size writes nothing. Each part of
   another type is written by that type's own function, so a recursive type
   needs nothing more. *)
let encode_signature t ty = debug_signature t ty

let encode_call t b ~output ty (place : Lir.place) =
  if not (Memory_layout.has_zero_size t.env ty) then
    emit b
      (Call
         {
           target = Direct { function_ = Instance (Encode ty); signature = encode_signature t ty };
           arguments = [ Lir.Address { place; writable = false }; output ];
           result = Discarded;
         })

let encode t ty =
  let b = create () in
  let parameter =
    if Memory_layout.has_zero_size t.env ty then None
    else Some (local b ~name:"value" (Pointer { target = Value ty; writable = false }))
  in
  let value : Lir.place =
    match parameter with Some p -> { root = Local p; projections = [ Deref ] } | None -> at 0
  in
  let out = local b ~name:"output" (output_parameter t) in
  let output = Lir.Copy (at out) in
  let encode_call = encode_call t b ~output in
  start b (block b);
  (* The value's own bytes, read as bytes whatever it is. *)
  let bytes (place : Lir.place) size =
    let first = local b (Raw (Pointer (Data (builtin UInt8)))) in
    emit b
      (Assign
         (at first, Convert (Address { place; writable = false }, Pointer (Data (builtin UInt8)))));
    write t b ~output "append" bytes_ty (bytes b ~elements:(Copy (at first)) ~length:(usize size))
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
     match t.representation ty with
     | Handle -> bug "a handle cannot be worked out while compiling"
     | Shared _ -> bug "a shared value cannot be worked out while compiling"
     | Storage element ->
         bytes (Storage.length value) (Memory_layout.of_type t.env t.usize).size;
         loop t b
           ~count:(Copy (Storage.length value))
           (fun index -> encode_call element (Storage.at value (Copy (at index))))
     | Shape (Scalar _) -> bytes value (Memory_layout.of_type t.env ty).size
     | Shape (Record members) -> fields value None members
     | Shape (Array (element, count)) ->
         loop t b ~count:(usize count) (fun index ->
             encode_call element (value / Index (Copy (at index))))
     | Shape (Sum variants) ->
         let after = block b in
         let cases =
           List.mapi
             (fun i (v : Memory_layout.variant_shape) ->
               let case = block b in
               aside b case (fun () ->
                   let index = local b (Raw (Integer UInt32)) in
                   emit b (Assign (at index, Use (Constant (Integer (UInt32, Z.of_int i)))));
                   bytes (at index) 4;
                   fields value (Some v.name) v.fields;
                   finish b (Goto after));
               (v.name, case))
             variants
         in
         finish b (Switch_variant { place = value; cases; default = None });
         start b after);
  finish b (Return None);
  instance (Encode ty) (build b ~parameters:(Option.to_list parameter @ [ out ]) ~result:None)
