let raise_bug format = Compiler_bug.raise_bug ~stage:"Writing" format
let output_ty = Storage.make_storage_type (Ground.make_builtin UInt8)
let bytes_ty = Storage.make_view_type (Ground.make_builtin UInt8)

let make_output_parameter env =
  match Convention.classify_parameter env Mut output_ty with
  | Some parameter -> parameter
  | None -> raise_bug "storage of no size"

let make_value_parameter ty = Lowered.Pointer { target = Value ty; writable = false }

let make_signature env parameters : Lowered.signature =
  { parameters = parameters @ [ make_output_parameter env ]; result = None; returns = true }

let emit_write_call env builder ~output (writer : Well_known.t) ty (place : Lowered.place) =
  let parameter, argument =
    match Convention.classify_parameter env Read ty with
    | Some (Pointer _ as parameter) -> (parameter, Lowered.Address { place; writable = false })
    | Some parameter -> (parameter, Copy place)
    | None -> raise_bug "%s is written, and has no size" (Ground.to_string ty)
  in
  Emit_c.Ir_builder.emit builder
    (Call
       {
         target =
           Direct
             {
               function_ =
                 Item (Lowered.Item.make_code (Well_known.make_path writer) Ground.no_instantiation);
               signature =
                 Convention.make_signature [ make_output_parameter env; parameter ] Nothing;
             };
         arguments = [ output; argument ];
         result = Discarded;
       })

let emit_write_bytes_call env builder ~output writer ~buffer ~length =
  let view = Emit_c.Ir_builder.allocate_local builder (Value bytes_ty) in
  Emit_c.Ir_builder.emit builder
    (Assign (Lowered.make_local_place view, Storage.build_view bytes_ty ~buffer ~length));
  emit_write_call env builder ~output writer bytes_ty (Lowered.make_local_place view)
