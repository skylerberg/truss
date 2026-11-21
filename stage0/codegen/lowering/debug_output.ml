let raise_bug format = Compiler_bug.raise_bug ~stage:"Debug_output" format

type form = Structure | Text | Sequence

let classify_form : Ground.ty -> form = function
  | Named { path; _ } -> (
      match Well_known.of_path path with
      | Some (String | String_slice) -> Text
      | Some (List | Slice) -> Sequence
      | _ -> Structure)
  | _ -> Structure

let int64 = Ground.make_builtin Int64
let uint64 = Ground.make_builtin UInt64

let make_signature env ty =
  Writing.make_signature env
    (if Memory_layout.has_zero_size env ty then [] else [ Writing.make_value_parameter ty ])

let write_text env builder ~output value =
  if value <> "" then
    Writing.emit_write_bytes_call env builder ~output Writing_append
      ~buffer:(Constant (Bytes value))
      ~length:(Lowered.make_uint64_constant (String.length value))

let emit_debug_call env builder ~output ty (place : Lowered.place) =
  let value_argument =
    if Memory_layout.has_zero_size env ty then []
    else [ Lowered.Address { place; writable = false } ]
  in
  Emit_c.Ir_builder.emit builder
    (Call
       {
         target = Direct { function_ = Item (Debug ty); signature = make_signature env ty };
         arguments = value_argument @ [ output ];
         result = Discarded;
       })

let write_scalar_debug env builder ~output (scalar : Memory_layout.scalar) (place : Lowered.place) =
  let write writer ty place = Writing.emit_write_call env builder ~output writer ty place in
  let write_widened writer wide (integer : Memory_layout.integer) =
    let value = Emit_c.Ir_builder.allocate_local builder (Value wide) in
    Emit_c.Ir_builder.emit builder
      (Assign (Lowered.make_local_place value, Convert (Copy place, Integer integer)));
    write writer wide (Lowered.make_local_place value)
  in
  match scalar with
  | Integer (Int8 | Int16 | Int32 | Int64) -> write_widened Writing_signed int64 Int64
  | Integer (UInt8 | UInt16 | UInt32 | UInt64) -> write_widened Writing_unsigned uint64 UInt64
  | Float32 -> write Float_text_write_shortest_float32 (Ground.make_builtin Float32) place
  | Float64 -> write Float_text_write_shortest_float64 (Ground.make_builtin Float64) place
  | Bool -> write Writing_boolean (Ground.make_builtin Bool) place
  | Character -> write Writing_quoted_character (Ground.make_builtin Character) place
  | Pointer _ | Nullable_pointer _ -> write_text env builder ~output "pointer"

let build_debug env ty =
  let builder = Emit_c.Ir_builder.create env ~item:(Debug ty) in
  let parameter =
    if Memory_layout.has_zero_size env ty then None
    else Some (Emit_c.Ir_builder.allocate_local builder (Writing.make_value_parameter ty))
  in
  let value : Lowered.place =
    match parameter with
    | Some parameter_local -> { root = Local parameter_local; projections = [ Deref ] }
    | None -> Lowered.make_local_place (Emit_c.Ir_builder.allocate_local builder (Value ty))
  in
  let output_pointer =
    Emit_c.Ir_builder.allocate_local builder (Writing.make_output_parameter env)
  in
  let output = Lowered.Copy (Lowered.make_local_place output_pointer) in
  let write_output_text = write_text env builder ~output in
  let emit_output_call = emit_debug_call env builder ~output in
  let rec write_list element ~index_element ~count =
    write_output_text "[";
    Emit_c.Ir_builder.emit_loop builder ~count (fun index ->
        Emit_c.Ir_builder.emit_when builder
          (Test (Not_equal, Copy (Lowered.make_local_place index), Lowered.make_uint64_constant 0))
          (fun () -> write_output_text ", ");
        emit_output_call element (index_element (Lowered.Copy (Lowered.make_local_place index))));
    write_output_text "]"
  and write_storage_or_view field_ty (place : Lowered.place) ~as_text =
    let element =
      match (Storage.find_storage_element field_ty, Storage.find_view_element field_ty) with
      | Some element, _ | None, Some element -> element
      | None, None -> raise_bug "%s is not storage or a view" (Ground.to_string field_ty)
    in
    let buffer = Storage.project_buffer place and count = Storage.project_length place in
    if as_text then
      Writing.emit_write_bytes_call env builder ~output Writing_quoted_text ~buffer:(Copy buffer)
        ~length:(Copy count)
    else
      write_list element
        ~index_element:(fun index -> Lowered.project buffer (Index index))
        ~count:(Copy count)
  and write_fields name (fields : (string * Memory_layout.member) list) project_field =
    write_output_text name;
    match fields with
    | [] -> ()
    | [ (field, Typed field_ty) ] ->
        write_output_text "(";
        emit_output_call field_ty (project_field field);
        write_output_text ")"
    | fields ->
        write_output_text "(";
        List.iteri
          (fun index (field, member) ->
            match member with
            | Memory_layout.Typed field_ty ->
                write_output_text ((if index > 0 then ", " else "") ^ field ^ ": ");
                emit_output_call field_ty (project_field field)
            | Raw _ -> ())
          fields;
        write_output_text ")"
  in
  (match (classify_form ty, Representation.classify env ty) with
  | (Text | Sequence), Shape (Record [ (field, Typed field_ty) ]) ->
      write_storage_or_view field_ty
        (Lowered.project value (Field field))
        ~as_text:(classify_form ty = Text)
  | _, Handle -> write_output_text "Handle"
  | _, Shared _ -> write_output_text "Shared"
  | _, Any -> write_output_text "any"
  | _, Storage element ->
      write_list element ~index_element:(Storage.index_element value)
        ~count:(Copy (Storage.project_length value))
  | _, Shape shape -> (
      match (ty, shape) with
      | Never, _ -> ()
      | Function _, _ -> write_output_text "fn"
      | _, Scalar scalar -> write_scalar_debug env builder ~output scalar value
      | Named { path; _ }, Record [] ->
          write_output_text
            (if Well_known.find_builtin_type path = Some Unit then Path.show_name path
             else Path.show_name path ^ "()")
      | Named { path; _ }, Record fields ->
          write_fields (Path.show_name path) fields (fun field ->
              Lowered.project value (Field field))
      | _, Record _ -> raise_bug "%s has the shape of a record and no name" (Ground.to_string ty)
      | _, Array (element, count) ->
          write_list element
            ~index_element:(fun index -> Lowered.project value (Index index))
            ~count:(Lowered.make_uint64_constant count)
      | _, Sum variants ->
          let after = Emit_c.Ir_builder.allocate_block builder in
          let cases =
            List.map
              (fun (variant_shape : Memory_layout.variant_shape) ->
                let case = Emit_c.Ir_builder.allocate_block builder in
                Emit_c.Ir_builder.run_in_block builder case (fun () ->
                    write_fields variant_shape.name variant_shape.fields (fun field ->
                        Lowered.project value
                          (Variant_field { variant = variant_shape.name; field }));
                    Emit_c.Ir_builder.finish builder (Goto after));
                (variant_shape.name, case))
              variants
          in
          Emit_c.Ir_builder.finish builder (Switch_variant { place = value; cases; default = None });
          Emit_c.Ir_builder.start builder after));
  Emit_c.Ir_builder.finish builder (Return None);
  Emit_c.Ir_builder.build builder
    { parameters = Option.to_list parameter @ [ output_pointer ]; result = None; returns = true }
