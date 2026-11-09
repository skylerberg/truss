let bug format = Printf.ksprintf (fun message -> invalid_arg ("Glue: " ^ message)) format

type kind = Shape of Memory_layout.shape | Storage of Ground.ty

module Types = Map.Make (struct
  type t = Ground.ty

  let compare = Ground.compare
end)

type debug_form = Structure | Text | Sequence

type t = {
  env : Memory_layout.env;
  kind_of : Ground.ty -> kind;
  usize : Ground.ty;
  debug_form : Ground.ty -> debug_form;
  mutable trivial_types : bool Types.t;
}

let create env ~kind_of ~usize ?(debug_form = fun _ -> Structure) () =
  { env; kind_of; usize; debug_form; trivial_types = Types.empty }

let rec trivial t ty =
  match Types.find_opt ty t.trivial_types with
  | Some answer -> answer
  | None ->
      (* A type that contains itself does so through an [indirect] variant
         or storage, so it is not trivial, which is the answer a cycle
         gets. *)
      t.trivial_types <- Types.add ty false t.trivial_types;
      let any = match ty with Ground.Any _ -> true | _ -> false in
      let member : Memory_layout.member -> bool = function
        | Typed ty -> trivial t ty
        | Raw _ -> true
      in
      let answer =
        if any then false
        else
          match t.kind_of ty with
          | Storage _ -> false
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

let loop t b ~count body = loop b ~usize:t.usize ~count body
let instance key main : Lir.t = { key; main; nested = [||] }

let variant_shapes t ty =
  match t.kind_of ty with
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
  (match (ty, t.kind_of ty) with
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
  | _, Storage element ->
      if not (trivial t element) then
        loop t b
          ~count:(Copy (value / Field "length"))
          (fun index -> emit b (Drop (value / Field "buffer" / Index (Copy (at index)))));
      let owned = local b (Raw Bool) in
      let free = block b in
      let after = block b in
      emit b (Assign (at owned, Binary (Not_equal, Copy (value / Field "capacity"), usize 0)));
      finish b (Switch { value = Copy (at owned); cases = [ (Z.one, free) ]; default = Some after });
      start b free;
      emit b
        (Call
           {
             target = Intrinsic Free;
             arguments = [ Copy (value / Field "buffer") ];
             result = Discarded;
           });
      finish b (Goto after);
      start b after
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
  let self_local = Option.map (fun ty -> local b ~name:"self" ty) parameter in
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
     match t.kind_of ty with
     | Storage element ->
         let layout = Memory_layout.of_type t.env element in
         let shared = local b (Raw Bool) in
         let empty = local b (Raw Bool) in
         let share = block b in
         let check = block b in
         let allocate = block b in
         let after = block b in
         (* Static bytes, an empty buffer, and elements of zero size are
            shared, not copied. *)
         emit b (Assign (at shared, Binary (Equal, Copy (self / Field "capacity"), usize 0)));
         finish b
           (Switch { value = Copy (at shared); cases = [ (Z.one, share) ]; default = Some check });
         start b check;
         emit b (Assign (at empty, Binary (Equal, Copy (self / Field "length"), usize 0)));
         finish b
           (Switch
              {
                value = Copy (at empty);
                cases = [ (Z.one, share) ];
                default = Some (if layout.size = 0 then share else allocate);
              });
         start b share;
         emit b (Assign (result, Use (Copy self)));
         finish b (Goto after);
         start b allocate;
         let bytes = local b (Value t.usize) in
         let buffer = local b ~name:"buffer" (Raw (Pointer (Data element))) in
         emit b
           (Assign (at bytes, Binary (Multiply, Copy (self / Field "length"), usize layout.size)));
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
                  arguments = [ Copy (at buffer); Copy (self / Field "buffer"); Copy (at bytes) ];
                  result = Discarded;
                })
         else
           loop t b
             ~count:(Copy (self / Field "length"))
             (fun index ->
               copy_into t b
                 ~destination:(at buffer / Index (Copy (at index)))
                 ~source:(self / Field "buffer" / Index (Copy (at index)))
                 element);
         emit b
           (Assign
              ( result,
                Build
                  {
                    ty;
                    variant = None;
                    fields =
                      [
                        ("buffer", Copy (at buffer));
                        ("length", Copy (self / Field "length"));
                        ("capacity", Copy (self / Field "length"));
                      ];
                  } ));
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
    (build b ~parameters
       ~result:
         (match convention with Returned ty -> Some ty | Nothing | Through_pointer _ -> None))

(* Debug output *)

let zero_size t ty = (Memory_layout.of_type t.env ty).size = 0

let debug_signature t ty : Lir.signature =
  {
    parameters =
      (if zero_size t ty then [] else [ Pointer { target = Value ty; writable = false } ]);
    result = None;
    returns = true;
  }

let text b value =
  if value <> "" then
    emit b
      (Call
         {
           target = Intrinsic Debug_text;
           arguments = [ Constant (Bytes value); usize (String.length value) ];
           result = Discarded;
         })

let debug_call t b ty (place : Lir.place) =
  let arguments = if zero_size t ty then [] else [ Lir.Address { place; writable = false } ] in
  emit b
    (Call
       {
         target = Direct { function_ = Instance (Debug ty); signature = debug_signature t ty };
         arguments;
         result = Discarded;
       })

let scalar_debug t b (scalar : Memory_layout.scalar) (place : Lir.place) =
  let call intrinsic operand =
    emit b (Call { target = Intrinsic intrinsic; arguments = [ operand ]; result = Discarded })
  in
  match scalar with
  | Integer (Int8 | Int16 | Int32 | Int64 | ISize) ->
      let wide = local b (Raw (Integer Int64)) in
      emit b (Assign (at wide, Convert (Copy place, Integer Int64)));
      call Debug_signed (Copy (at wide))
  | Integer (UInt8 | UInt16 | UInt32 | UInt64 | USize) ->
      let wide = local b (Raw (Integer UInt64)) in
      emit b (Assign (at wide, Convert (Copy place, Integer UInt64)));
      call Debug_unsigned (Copy (at wide))
  | Float32 -> call Debug_float32 (Copy place)
  | Float64 -> call Debug_float64 (Copy place)
  | Bool -> call Debug_bool (Copy place)
  | Character -> call Debug_character (Copy place)
  | Pointer _ | Nullable_pointer _ -> text b "pointer"

let debug t ty =
  let b = create () in
  let parameter =
    if zero_size t ty then None
    else Some (local b ~name:"value" (Pointer { target = Value ty; writable = false }))
  in
  let value : Lir.place =
    match parameter with Some p -> { root = Local p; projections = [ Deref ] } | None -> at 0
  in
  start b (block b);
  let rec list_of element ~element_at ~count =
    text b "[";
    loop t b ~count (fun index ->
        let later = local b (Raw Bool) in
        emit b (Assign (at later, Binary (Not_equal, Copy (at index), usize 0)));
        when_ b (Copy (at later)) (fun () -> text b ", ");
        debug_call t b element (element_at (Lir.Copy (at index))));
    text b "]"
  and storage_or_view field_ty (place : Lir.place) ~as_text =
    let element, buffer =
      match t.kind_of field_ty with
      | Storage element -> (element, place / Field "buffer")
      | Shape (Record [ ("elements", Raw (Pointer (Data element))); _ ]) ->
          (element, place / Field "elements")
      | _ -> bug "%s is not storage or a view" (Ground.to_string field_ty)
    in
    if as_text then
      emit b
        (Call
           {
             target = Intrinsic Debug_string;
             arguments = [ Copy buffer; Copy (place / Field "length") ];
             result = Discarded;
           })
    else
      list_of element ~element_at:(fun i -> buffer / Index i) ~count:(Copy (place / Field "length"))
  and fields_debug name (fields : (string * Memory_layout.member) list) field_place =
    text b name;
    match fields with
    | [] -> ()
    | [ (field, Typed field_ty) ] ->
        text b "(";
        debug_call t b field_ty (field_place field);
        text b ")"
    | fields ->
        text b "(";
        List.iteri
          (fun i (field, member) ->
            match member with
            | Memory_layout.Typed field_ty ->
                text b ((if i > 0 then ", " else "") ^ field ^ ": ");
                debug_call t b field_ty (field_place field)
            | Raw _ -> ())
          fields;
        text b ")"
  in
  (match (t.debug_form ty, t.kind_of ty) with
  | (Text | Sequence), Shape (Record [ (field, Typed field_ty) ]) ->
      storage_or_view field_ty (value / Field field) ~as_text:(t.debug_form ty = Text)
  | _, Storage element ->
      list_of element
        ~element_at:(fun i -> value / Field "buffer" / Index i)
        ~count:(Copy (value / Field "length"))
  | _, Shape shape -> (
      match (ty, shape) with
      | Never, _ -> ()
      | Function _, _ -> text b "fn"
      | Any _, _ -> text b "any"
      | Cursor _, _ -> text b "cursor"
      | _, Scalar scalar -> scalar_debug t b scalar value
      | Named { path; _ }, Record [] ->
          text b (if Ground.path_name path = "Unit" then "Unit" else Ground.path_name path ^ "()")
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
  instance (Debug ty) (build b ~parameters:(Option.to_list parameter) ~result:None)
