let bug format = Compiler_bug.bug ~stage:"Encoding" format
let variant_index : Memory_layout.integer = UInt32
let make_signature env ty = Writing.make_signature env [ Writing.make_value_parameter ty ]

let encode_call env builder ~output ty (place : Lowered.place) =
  if not (Memory_layout.has_zero_size env ty) then
    Emit_c.Builder.emit builder
      (Call
         {
           target = Direct { function_ = Instance (Encode ty); signature = make_signature env ty };
           arguments = [ Lowered.Address { place; writable = false }; output ];
           result = Discarded;
         })

let encode env ty =
  let builder = Emit_c.Builder.create env ~key:(Encode ty) in
  let parameter =
    Emit_c.Builder.allocate_local builder ~name:"value" (Writing.make_value_parameter ty)
  in
  let value : Lowered.place = { root = Local parameter; projections = [ Deref ] } in
  let output_pointer =
    Emit_c.Builder.allocate_local builder ~name:"output" (Writing.make_output_parameter env)
  in
  let output = Lowered.Copy (Lowered.make_local_place output_pointer) in
  let encode_call = encode_call env builder ~output in
  Emit_c.Builder.start builder (Emit_c.Builder.allocate_block builder);
  let append_bytes (place : Lowered.place) size =
    let byte = Ground.make_builtin UInt8 in
    let first = Emit_c.Builder.allocate_local builder (Raw (Pointer (Data byte))) in
    Emit_c.Builder.emit builder
      (Assign
         ( Lowered.make_local_place first,
           Convert (Address { place; writable = false }, Pointer (Data byte)) ));
    Writing.emit_write_bytes_call env builder ~output Writing_append
      ~elements:(Copy (Lowered.make_local_place first))
      ~length:(Lowered.make_uint64_constant size)
  in
  let fields place variant (fields : (string * Memory_layout.member) list) =
    List.iter
      (fun (name, member) ->
        match member with
        | Memory_layout.Typed field_ty ->
            encode_call field_ty
              (match variant with
              | None -> Lowered.project place (Field name)
              | Some variant -> Lowered.project place (Variant_field { variant; field = name }))
        | Raw _ -> bug "a raw field in a value written out")
      fields
  in
  (match Representation.classify env ty with
  | Handle -> bug "a handle cannot be computed while compiling"
  | Shared _ -> bug "a shared value cannot be computed while compiling"
  | Any -> bug "an any value cannot be computed while compiling"
  | Storage element ->
      append_bytes (Storage.project_length value) (Memory_layout.compute_integer_size UInt64);
      Emit_c.Builder.emit_loop builder
        ~count:(Copy (Storage.project_length value))
        (fun index ->
          encode_call element (Storage.index_element value (Copy (Lowered.make_local_place index))))
  | Shape (Scalar _) -> append_bytes value (Memory_layout.of_type env ty).size
  | Shape (Record members) -> fields value None members
  | Shape (Array (element, count)) ->
      Emit_c.Builder.emit_loop builder ~count:(Lowered.make_uint64_constant count) (fun index ->
          encode_call element
            (Lowered.project value (Index (Copy (Lowered.make_local_place index)))))
  | Shape (Sum variants) ->
      let after = Emit_c.Builder.allocate_block builder in
      let cases =
        List.mapi
          (fun index (variant_shape : Memory_layout.variant_shape) ->
            let case = Emit_c.Builder.allocate_block builder in
            Emit_c.Builder.in_block builder case (fun () ->
                let encoded_index =
                  Emit_c.Builder.allocate_local builder (Raw (Integer variant_index))
                in
                Emit_c.Builder.emit builder
                  (Assign
                     ( Lowered.make_local_place encoded_index,
                       Use (Constant (Integer (variant_index, Z.of_int index))) ));
                append_bytes
                  (Lowered.make_local_place encoded_index)
                  (Memory_layout.compute_integer_size variant_index);
                fields value (Some variant_shape.name) variant_shape.fields;
                Emit_c.Builder.finish builder (Goto after));
            (variant_shape.name, case))
          variants
      in
      Emit_c.Builder.finish builder (Switch_variant { place = value; cases; default = None });
      Emit_c.Builder.start builder after);
  Emit_c.Builder.finish builder (Return None);
  Emit_c.Builder.build builder
    { parameters = [ parameter; output_pointer ]; result = None; returns = true }

type reader = { encoded : string; mutable offset : int }

let is_at_end reader = reader.offset = String.length reader.encoded

let take reader count =
  if reader.offset + count > String.length reader.encoded then
    bug "a value written out while compiling ends early";
  let part = String.sub reader.encoded reader.offset count in
  reader.offset <- reader.offset + count;
  part

let decode_unsigned bytes =
  let value = ref Z.zero in
  for index = String.length bytes - 1 downto 0 do
    value := Z.add (Z.shift_left !value 8) (Z.of_int (Char.code bytes.[index]))
  done;
  !value

let decode_integer reader (kind : Memory_layout.integer) =
  let size = Memory_layout.compute_integer_size kind in
  let value = decode_unsigned (take reader size) in
  match kind with
  | Int8 | Int16 | Int32 | Int64 ->
      if Z.testbit value ((8 * size) - 1) then Z.sub value (Z.shift_left Z.one (8 * size))
      else value
  | UInt8 | UInt16 | UInt32 | UInt64 -> value

let decode_scalar reader (kind : Memory_layout.scalar) : Lowered.constant =
  match kind with
  | Integer kind -> Integer (kind, decode_integer reader kind)
  | Float32 -> Float32 (Z.to_int32_unsigned (decode_unsigned (take reader 4)))
  | Float64 -> Float64 (Z.to_int64_unsigned (decode_unsigned (take reader 8)))
  | Bool -> Bool (decode_unsigned (take reader 1) <> Z.zero)
  | Character -> Character (Z.to_int (decode_unsigned (take reader 4)))
  | Pointer _ | Nullable_pointer _ -> bug "a pointer computed while compiling"

let decode env ty encoded : Lowered.static_value =
  let reader = { encoded; offset = 0 } in
  let rec value ty : Lowered.static_value =
    if Memory_layout.has_zero_size env ty then empty ty
    else
      match Representation.classify env ty with
      | Handle -> bug "a handle computed while compiling"
      | Shared _ -> bug "a shared value computed while compiling"
      | Any -> bug "an any value computed while compiling"
      | Storage element ->
          let count = Z.to_int (decode_integer reader UInt64) in
          Static_storage { element; elements = List.init count (fun _ -> value element) }
      | Shape (Scalar kind) -> Static_scalar (decode_scalar reader kind)
      | Shape (Record members) -> Static_record (fields members)
      | Shape (Array (element, count)) -> Static_array (List.init count (fun _ -> value element))
      | Shape (Sum variants) ->
          let variant = List.nth variants (Z.to_int (decode_integer reader variant_index)) in
          Static_variant (variant.name, fields variant.fields)
  and fields members =
    List.map
      (fun (name, (member : Memory_layout.member)) ->
        match member with
        | Typed field_ty -> (name, value field_ty)
        | Raw _ -> bug "a raw field computed while compiling")
      members
  and empty ty : Lowered.static_value =
    match Memory_layout.shape env ty with
    | Record members ->
        Static_record (List.map (fun (name, member) -> (name, empty_member member)) members)
    | Sum [ variant ] ->
        Static_variant
          (variant.name, List.map (fun (name, member) -> (name, empty_member member)) variant.fields)
    | Array (element, count) -> Static_array (List.init count (fun _ -> empty element))
    | _ -> bug "%s has no one value of zero size" (Ground.to_string ty)
  and empty_member : Memory_layout.member -> Lowered.static_value = function
    | Typed ty -> empty ty
    | Raw _ -> bug "a raw field of zero size"
  in
  let decoded = value ty in
  if not (is_at_end reader) then bug "a value written out while compiling has bytes left over";
  decoded

let decode_booleans encoded =
  let reader = { encoded; offset = 0 } in
  let rec booleans () =
    if is_at_end reader then []
    else
      match decode_scalar reader Bool with
      | Bool holds -> holds :: booleans ()
      | _ -> bug "a Bool written out while compiling reads back as another scalar"
  in
  booleans ()
