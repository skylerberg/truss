let bug format = Compiler_bug.bug ~stage:"Encoding" format
let variant_index : Memory_layout.integer = UInt32

module Builder = Emit_c.Builder

let signature env ty = Writing.signature env [ Writing.value_parameter ty ]

let encode_call env builder ~output ty (place : Lowered.place) =
  if not (Memory_layout.has_zero_size env ty) then
    Builder.emit builder
      (Call
         {
           target = Direct { function_ = Instance (Encode ty); signature = signature env ty };
           arguments = [ Lowered.Address { place; writable = false }; output ];
           result = Discarded;
         })

let encode env ty =
  let builder = Builder.create env ~key:(Encode ty) in
  let parameter = Builder.local builder ~name:"value" (Writing.value_parameter ty) in
  let value : Lowered.place = { root = Local parameter; projections = [ Deref ] } in
  let output_pointer = Builder.local builder ~name:"output" (Writing.output_parameter env) in
  let output = Lowered.Copy (Builder.at output_pointer) in
  let encode_call = encode_call env builder ~output in
  Builder.start builder (Builder.block builder);
  let append_bytes (place : Lowered.place) size =
    let byte = Ground.builtin UInt8 in
    let first = Builder.local builder (Raw (Pointer (Data byte))) in
    Builder.emit builder
      (Assign (Builder.at first, Convert (Address { place; writable = false }, Pointer (Data byte))));
    Writing.call_with_bytes env builder ~output Writing_append
      ~elements:(Copy (Builder.at first))
      ~length:(Builder.constant_uint64 size)
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
      append_bytes (Storage.project_length value) (Memory_layout.integer_size UInt64);
      Builder.loop builder
        ~count:(Copy (Storage.project_length value))
        (fun index -> encode_call element (Storage.index_element value (Copy (Builder.at index))))
  | Shape (Scalar _) -> append_bytes value (Memory_layout.of_type env ty).size
  | Shape (Record members) -> fields value None members
  | Shape (Array (element, count)) ->
      Builder.loop builder ~count:(Builder.constant_uint64 count) (fun index ->
          encode_call element (Lowered.project value (Index (Copy (Builder.at index)))))
  | Shape (Sum variants) ->
      let after = Builder.block builder in
      let cases =
        List.mapi
          (fun index (variant_shape : Memory_layout.variant_shape) ->
            let case = Builder.block builder in
            Builder.in_block builder case (fun () ->
                let encoded_index = Builder.local builder (Raw (Integer variant_index)) in
                Builder.emit builder
                  (Assign
                     ( Builder.at encoded_index,
                       Use (Constant (Integer (variant_index, Z.of_int index))) ));
                append_bytes (Builder.at encoded_index) (Memory_layout.integer_size variant_index);
                fields value (Some variant_shape.name) variant_shape.fields;
                Builder.finish builder (Goto after));
            (variant_shape.name, case))
          variants
      in
      Builder.finish builder (Switch_variant { place = value; cases; default = None });
      Builder.start builder after);
  Builder.finish builder (Return None);
  Builder.build builder
    { parameters = [ parameter; output_pointer ]; result = None; returns = true }

type reader = { encoded : string; mutable offset : int }

let is_at_end reader = reader.offset = String.length reader.encoded

let take reader count =
  if reader.offset + count > String.length reader.encoded then
    bug "a value written out while compiling ends early";
  let part = String.sub reader.encoded reader.offset count in
  reader.offset <- reader.offset + count;
  part

let unsigned bytes =
  let value = ref Z.zero in
  for index = String.length bytes - 1 downto 0 do
    value := Z.add (Z.shift_left !value 8) (Z.of_int (Char.code bytes.[index]))
  done;
  !value

let integer reader (kind : Memory_layout.integer) =
  let size = Memory_layout.integer_size kind in
  let value = unsigned (take reader size) in
  match kind with
  | Int8 | Int16 | Int32 | Int64 ->
      if Z.testbit value ((8 * size) - 1) then Z.sub value (Z.shift_left Z.one (8 * size))
      else value
  | UInt8 | UInt16 | UInt32 | UInt64 -> value

let scalar reader (kind : Memory_layout.scalar) : Lowered.constant =
  match kind with
  | Integer kind -> Integer (kind, integer reader kind)
  | Float32 -> Float32 (Z.to_int32_unsigned (unsigned (take reader 4)))
  | Float64 -> Float64 (Z.to_int64_unsigned (unsigned (take reader 8)))
  | Bool -> Bool (unsigned (take reader 1) <> Z.zero)
  | Character -> Character (Z.to_int (unsigned (take reader 4)))
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
          let count = Z.to_int (integer reader UInt64) in
          Static_storage { element; elements = List.init count (fun _ -> value element) }
      | Shape (Scalar kind) -> Static_scalar (scalar reader kind)
      | Shape (Record members) -> Static_record (fields members)
      | Shape (Array (element, count)) -> Static_array (List.init count (fun _ -> value element))
      | Shape (Sum variants) ->
          let variant = List.nth variants (Z.to_int (integer reader variant_index)) in
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
      match scalar reader Bool with
      | Bool holds -> holds :: booleans ()
      | _ -> bug "a Bool written out while compiling reads back as another scalar"
  in
  booleans ()
