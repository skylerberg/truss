let bug format = Compiler_bug.bug ~stage:"Debug_output" format

type form = Structure | Text | Sequence

let form : Ground.ty -> form = function
  | Named { path; _ } -> (
      match Well_known.of_path path with
      | Some (String | String_slice) -> Text
      | Some (List | Slice) -> Sequence
      | _ -> Structure)
  | _ -> Structure

let int64 = Ground.builtin Int64
let uint64 = Ground.builtin UInt64

let signature env ty =
  Writing.signature env
    (if Memory_layout.has_zero_size env ty then [] else [ Writing.value_parameter ty ])

let text env builder ~output value =
  if value <> "" then
    Writing.call_with_bytes env builder ~output Writing_append ~elements:(Constant (Bytes value))
      ~length:(Lowered.make_uint64_constant (String.length value))

let debug_call env builder ~output ty (place : Lowered.place) =
  let value_argument =
    if Memory_layout.has_zero_size env ty then []
    else [ Lowered.Address { place; writable = false } ]
  in
  Emit_c.Builder.emit builder
    (Call
       {
         target = Direct { function_ = Instance (Debug ty); signature = signature env ty };
         arguments = value_argument @ [ output ];
         result = Discarded;
       })

let scalar_debug env builder ~output (scalar : Memory_layout.scalar) (place : Lowered.place) =
  let write writer ty place = Writing.call env builder ~output writer ty place in
  let widened writer wide (integer : Memory_layout.integer) =
    let value = Emit_c.Builder.local builder (Value wide) in
    Emit_c.Builder.emit builder
      (Assign (Lowered.make_local_place value, Convert (Copy place, Integer integer)));
    write writer wide (Lowered.make_local_place value)
  in
  match scalar with
  | Integer (Int8 | Int16 | Int32 | Int64) -> widened Writing_signed int64 Int64
  | Integer (UInt8 | UInt16 | UInt32 | UInt64) -> widened Writing_unsigned uint64 UInt64
  | Float32 -> write Writing_float32 (Ground.builtin Float32) place
  | Float64 -> write Writing_float64 (Ground.builtin Float64) place
  | Bool -> write Writing_boolean (Ground.builtin Bool) place
  | Character -> write Writing_quoted_character (Ground.builtin Character) place
  | Pointer _ | Nullable_pointer _ -> text env builder ~output "pointer"

let debug env ty =
  let builder = Emit_c.Builder.create env ~key:(Debug ty) in
  let parameter =
    if Memory_layout.has_zero_size env ty then None
    else Some (Emit_c.Builder.local builder ~name:"value" (Writing.value_parameter ty))
  in
  let value : Lowered.place =
    match parameter with
    | Some parameter_local -> { root = Local parameter_local; projections = [ Deref ] }
    | None -> Lowered.make_local_place 0
  in
  let output_pointer = Emit_c.Builder.local builder ~name:"output" (Writing.output_parameter env) in
  let output = Lowered.Copy (Lowered.make_local_place output_pointer) in
  let text = text env builder ~output in
  let debug_call = debug_call env builder ~output in
  Emit_c.Builder.start builder (Emit_c.Builder.block builder);
  let rec list_of element ~element_at ~count =
    text "[";
    Emit_c.Builder.loop builder ~count (fun index ->
        let is_after_first = Emit_c.Builder.local builder (Raw Bool) in
        Emit_c.Builder.emit builder
          (Assign
             ( Lowered.make_local_place is_after_first,
               Binary
                 (Not_equal, Copy (Lowered.make_local_place index), Lowered.make_uint64_constant 0)
             ));
        Emit_c.Builder.when_ builder
          (Copy (Lowered.make_local_place is_after_first))
          (fun () -> text ", ");
        debug_call element (element_at (Lowered.Copy (Lowered.make_local_place index))));
    text "]"
  and storage_or_view field_ty (place : Lowered.place) ~as_text =
    let element, buffer, count =
      match (Storage.match_storage_element field_ty, Storage.match_view_element field_ty) with
      | Some element, _ -> (element, Storage.project_buffer place, Storage.project_length place)
      | None, Some element ->
          (element, Storage.project_view_elements place, Storage.project_view_length place)
      | None, None -> bug "%s is not storage or a view" (Ground.to_string field_ty)
    in
    if as_text then
      Writing.call_with_bytes env builder ~output Writing_quoted_text ~elements:(Copy buffer)
        ~length:(Copy count)
    else
      list_of element
        ~element_at:(fun index -> Lowered.project buffer (Index index))
        ~count:(Copy count)
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
  (match (form ty, Representation.classify env ty) with
  | (Text | Sequence), Shape (Record [ (field, Typed field_ty) ]) ->
      storage_or_view field_ty (Lowered.project value (Field field)) ~as_text:(form ty = Text)
  | _, Handle -> text "Handle"
  | _, Shared _ -> text "Shared"
  | _, Any -> text "any"
  | _, Storage element ->
      list_of element ~element_at:(Storage.index_element value)
        ~count:(Copy (Storage.project_length value))
  | _, Shape shape -> (
      match (ty, shape) with
      | Never, _ -> ()
      | Function _, _ -> text "fn"
      | _, Scalar scalar -> scalar_debug env builder ~output scalar value
      | Named { path; _ }, Record [] ->
          text (if Ground.path_name path = "Unit" then "Unit" else Ground.path_name path ^ "()")
      | Named { path; _ }, Record fields ->
          fields_debug (Ground.path_name path) fields (fun field ->
              Lowered.project value (Field field))
      | _, Record _ -> bug "%s has the shape of a record and no name" (Ground.to_string ty)
      | _, Array (element, count) ->
          list_of element
            ~element_at:(fun index -> Lowered.project value (Index index))
            ~count:(Lowered.make_uint64_constant count)
      | _, Sum variants ->
          let after = Emit_c.Builder.block builder in
          let cases =
            List.map
              (fun (variant_shape : Memory_layout.variant_shape) ->
                let case = Emit_c.Builder.block builder in
                Emit_c.Builder.in_block builder case (fun () ->
                    fields_debug variant_shape.name variant_shape.fields (fun field ->
                        Lowered.project value
                          (Variant_field { variant = variant_shape.name; field }));
                    Emit_c.Builder.finish builder (Goto after));
                (variant_shape.name, case))
              variants
          in
          Emit_c.Builder.finish builder (Switch_variant { place = value; cases; default = None });
          Emit_c.Builder.start builder after));
  Emit_c.Builder.finish builder (Return None);
  Emit_c.Builder.build builder
    { parameters = Option.to_list parameter @ [ output_pointer ]; result = None; returns = true }
