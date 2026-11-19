let raise_bug format = Context.raise_bug format
let byte = Ground.make_builtin UInt8

let make_number_constant (context : Context.t) number : Lowered.operand =
  let env = context.env in
  let classify_scalar = Context.classify_scalar in
  let integer =
    match
      classify_scalar env
        (Ground.make_builtin (Intrinsic.convert_libc_scalar (Libc.classify_number number)))
    with
    | Integer integer -> integer
    | _ -> raise_bug "a number of the C library that is not an integer"
  in
  Constant (Integer (integer, Z.of_int (Libc.evaluate_number (Memory_layout.system env) number)))

let load_text_at (context : Context.t) address ~is_present =
  let builder = context.builder in
  let set = Context.set context in
  let call = Context.call context in
  let allocate_uint64_local () = Context.allocate_uint64_local context in
  Emit_c.Ir_builder.emit builder
    (Assign (is_present, Compare (Not_equal, Copy (Lowered.make_local_place address), Constant Null)));
  let elements = Emit_c.Ir_builder.allocate_local builder (Raw (Pointer (Data byte))) in
  let count = allocate_uint64_local () in
  Emit_c.Ir_builder.emit builder
    (Assign (Lowered.make_local_place elements, Use (Constant Storage.empty_buffer)));
  Emit_c.Ir_builder.emit builder
    (Assign (Lowered.make_local_place count, Use (Lowered.make_uint64_constant 0)));
  Emit_c.Ir_builder.emit_when builder (Holds (Copy is_present)) (fun () ->
      Emit_c.Ir_builder.emit builder
        (Assign (Lowered.make_local_place elements, Use (Copy (Lowered.make_local_place address))));
      call ~result:(Lowered.make_local_place count) Terminated_length
        [ Copy (Lowered.make_local_place address) ]);
  set
    (Storage.build_view (Storage.make_view_type byte)
       ~buffer:(Copy (Lowered.make_local_place elements))
       ~length:(Copy (Lowered.make_local_place count)))

let lower (context : Context.t) (function_ : Libc.function_) =
  let index_element = Storage.index_element in
  let builder = context.builder in
  let env = context.env in
  let destination = context.destination in
  let set = Context.set context in
  let read_argument = Context.read_argument context in
  let read_operand = Context.read_operand context in
  let emit_uint64 = Context.emit_uint64 context in
  let fail = Context.fail context in
  let fail_obligation_when = Context.fail_obligation_when context in
  let compute_room = Context.compute_room context in
  let copy_length = Context.copy_length in
  let extract_place = Context.extract_place in
  let classify_scalar = Context.classify_scalar in
  if not (Libc.is_available (Memory_layout.system env) function_) then begin
    fail Panic (Printf.sprintf "this system's C library has no %s" (Libc.show_function function_));
    Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder)
  end
  else begin
    let ground scalar = Ground.make_builtin (Intrinsic.convert_libc_scalar scalar) in
    let { Libc.parameters; result; _ } = Libc.make_signature function_ in
    let after = ref [] in
    let next = ref 0 in
    let take_argument_index () =
      let index = !next in
      incr next;
      index
    in
    let call_arguments =
      List.map
        (fun (_, (passes : Libc.passes)) : Lowered.operand ->
          match passes with
          | Value _ -> read_operand (take_argument_index ())
          | Elements _ ->
              Copy (Storage.project_buffer (extract_place (read_argument (take_argument_index ()))))
          | Room _ ->
              let storage = extract_place (read_argument (take_argument_index ())) in
              Address { place = index_element storage (copy_length storage); writable = true }
          | Elements_to_change _ ->
              Copy (Storage.project_buffer (extract_place (read_argument (take_argument_index ()))))
          | Written (scalar, names) ->
              let structure =
                Emit_c.Ir_builder.allocate_local builder
                  (Value
                     (Ground.make_builtin Array
                        ~arguments:[ Type (ground scalar); Value (Z.of_int (List.length names)) ]))
              in
              List.iteri
                (fun index _ ->
                  let written = extract_place (read_argument (take_argument_index ())) in
                  Emit_c.Ir_builder.emit builder
                    (Assign
                       ( Lowered.project
                           (Lowered.make_local_place structure)
                           (Index (Lowered.make_uint64_constant index)),
                         Use (Copy written) ));
                  after :=
                    (fun () ->
                      Emit_c.Ir_builder.emit builder
                        (Assign
                           ( written,
                             Use
                               (Copy
                                  (Lowered.project
                                     (Lowered.make_local_place structure)
                                     (Index (Lowered.make_uint64_constant index)))) )))
                    :: !after)
                names;
              Address { place = Lowered.make_local_place structure; writable = true }
          | Always number -> Lowered.make_uint64_constant number
          | Fixed number -> make_number_constant context number)
        parameters
    in
    let position = ref 0 in
    let passed =
      List.concat_map
        (fun (name, (passes : Libc.passes)) ->
          match passes with
          | Value _ | Elements _ | Room _ | Elements_to_change _ ->
              let index = !position in
              incr position;
              [ (name, Some passes, index) ]
          | Written (_, names) ->
              List.map
                (fun name ->
                  let index = !position in
                  incr position;
                  (name, None, index))
                names
          | Always _ | Fixed _ -> [])
        parameters
    in
    let cast_to_uint64 operand = emit_uint64 (Convert (operand, Integer UInt64)) in
    let find_count (extent : Libc.extent) : Lowered.operand option =
      match extent with
      | Counted { by; each } -> (
          match List.find_opt (fun (name, _, _) -> name = by) passed with
          | Some (_, _, index) ->
              let count = cast_to_uint64 (read_operand index) in
              if each = 1 then Some count
              else Some (emit_uint64 (Binary (Multiply, count, Lowered.make_uint64_constant each)))
          | None -> raise_bug "a C library row counts by %s, which it does not take" by)
      | Exactly elements -> Some (Lowered.make_uint64_constant elements)
      | Number number -> Some (cast_to_uint64 (make_number_constant context number))
      | Through_zero -> None
    in
    List.iter
      (fun (_, (passes : Libc.passes option), index) ->
        match passes with
        | Some (Room (_, extent)) ->
            Option.iter
              (fun count ->
                fail_obligation_when
                  (Test (Greater, count, compute_room (extract_place (read_argument index))))
                  "a call of the C library with less room than it writes")
              (find_count extent)
        | Some (Elements_to_change (_, extent)) ->
            Option.iter
              (fun count ->
                fail_obligation_when
                  (Test (Greater, count, copy_length (extract_place (read_argument index))))
                  "a call of the C library with fewer elements than it mutates")
              (find_count extent)
        | Some (Elements (element, extent)) -> (
            let view = extract_place (read_argument index) in
            match find_count extent with
            | Some count ->
                fail_obligation_when
                  (Test (Greater, count, copy_length view))
                  "a call of the C library with fewer elements than it reads"
            | None ->
                let message = "a call of the C library with text that does not end with a zero" in
                let zero : Lowered.operand =
                  match classify_scalar env (ground element) with
                  | Integer integer -> Constant (Integer (integer, Z.zero))
                  | _ -> raise_bug "a C library row reads up to a zero that is not an integer"
                in
                fail_obligation_when
                  (Test (Equal, copy_length view, Lowered.make_uint64_constant 0))
                  message;
                let last =
                  emit_uint64 (Binary (Subtract, copy_length view, Lowered.make_uint64_constant 1))
                in
                fail_obligation_when
                  (Test (Not_equal, Copy (Storage.index_element view last), zero))
                  message)
        | Some (Value _ | Written _ | Always _ | Fixed _) | None -> ())
      passed;
    let target = Lowered.Foreign (Libc.make_declaration (Memory_layout.system env) function_) in
    let emit_bracket intrinsic =
      if Libc.is_blocking function_ then
        Emit_c.Ir_builder.emit builder
          (Call { target = Intrinsic intrinsic; arguments = []; result = Discarded })
    in
    let call result =
      emit_bracket Blocking_begin;
      Emit_c.Ir_builder.emit builder (Call { target; arguments = call_arguments; result });
      emit_bracket Blocking_end;
      List.iter (fun write -> write ()) (List.rev !after)
    in
    match result with
    | Returns _ -> call (match destination with Some place -> Returned place | None -> Discarded)
    | Never ->
        call Discarded;
        Emit_c.Ir_builder.finish builder Unreachable;
        Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder)
    | Points_at scalar ->
        let address =
          Emit_c.Ir_builder.allocate_local builder (Raw (Pointer (Data (ground scalar))))
        in
        call (Returned (Lowered.make_local_place address));
        set (Use (Copy (Lowered.project (Lowered.make_local_place address) Deref)))
    | Text ->
        let address =
          Emit_c.Ir_builder.allocate_local builder (Raw (Nullable_pointer (Data byte)))
        in
        call (Returned (Lowered.make_local_place address));
        load_text_at context address
          ~is_present:(extract_place (read_argument (take_argument_index ())))
  end
