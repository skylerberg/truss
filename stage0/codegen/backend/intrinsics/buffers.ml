let raise_bug format = Context.raise_bug format

let lower (context : Context.t) (buffer : Intrinsic.buffer) =
  let builder = context.builder in
  let env = context.env in
  let set = Context.set context in
  let read_argument = Context.read_argument context in
  let read_operand = Context.read_operand context in
  let read_type_argument = Context.read_type_argument context in
  let call = Context.call context in
  let allocate_uint64_local () = Context.allocate_uint64_local context in
  let emit_uint64 = Context.emit_uint64 context in
  let emit_bool = Context.emit_bool context in
  let fail_when = Context.fail_when context in
  let fail_obligation_when = Context.fail_obligation_when context in
  let check_index = Context.check_index context in
  let compute_room = Context.compute_room context in
  let read_array_length () = Context.read_array_length context in
  let copy_length = Context.copy_length in
  let index_element = Storage.index_element in
  let extract_place = Context.extract_place in
  let read = Context.read in
  let read_element_type () = read_type_argument 0 in
  let make_array_type count =
    Ground.make_builtin Array ~arguments:[ Type (read_element_type ()); Value count ]
  in
  let compute_element_layout () = Memory_layout.of_type env (read_element_type ()) in
  let element_size () = Lowered.make_uint64_constant (compute_element_layout ()).size in
  let resize_buffer storage capacity =
    let layout = compute_element_layout () in
    let bytes = allocate_uint64_local ()
    and too_many = Emit_c.Ir_builder.allocate_local builder (Raw Bool) in
    call
      ~result:(Lowered.make_local_place too_many)
      Multiply_overflow
      [
        capacity;
        Lowered.make_uint64_constant layout.size;
        Address { place = Lowered.make_local_place bytes; writable = true };
      ];
    fail_when Panic (Holds (Copy (Lowered.make_local_place too_many))) "out of memory";
    let buffer = Emit_c.Ir_builder.allocate_local builder (Raw (Pointer Opaque)) in
    Emit_c.Ir_builder.emit_if builder
      (Test (Storage.make_owned_block_test storage))
      ~yes:(fun () ->
        let held =
          emit_uint64
            (Binary
               ( Multiply,
                 Copy (Storage.project_capacity storage),
                 Lowered.make_uint64_constant layout.size ))
        in
        call ~result:(Lowered.make_local_place buffer) Reallocate
          [
            Copy (Storage.project_buffer storage);
            held;
            Copy (Lowered.make_local_place bytes);
            Lowered.make_uint64_constant layout.alignment;
          ])
      ~no:(fun () ->
        call ~result:(Lowered.make_local_place buffer) Allocate
          [ Copy (Lowered.make_local_place bytes); Lowered.make_uint64_constant layout.alignment ]);
    Emit_c.Ir_builder.emit builder
      (Assign (Storage.project_buffer storage, Use (Copy (Lowered.make_local_place buffer))));
    Emit_c.Ir_builder.emit builder (Assign (Storage.project_capacity storage, Use capacity))
  in
  let add_to_length storage amount =
    Emit_c.Ir_builder.emit builder
      (Assign (Storage.project_length storage, Binary (Add, copy_length storage, amount)))
  in
  match buffer with
  | Compare_bytes ->
      let left = extract_place (read_argument 0) and right = extract_place (read_argument 1) in
      let count = allocate_uint64_local () in
      Emit_c.Ir_builder.emit builder
        (Assign (Lowered.make_local_place count, Use (copy_length right)));
      Emit_c.Ir_builder.emit_when builder
        (Test (Less, copy_length left, copy_length right))
        (fun () ->
          Emit_c.Ir_builder.emit builder
            (Assign (Lowered.make_local_place count, Use (copy_length left))));
      let order = Emit_c.Ir_builder.allocate_local builder (Raw (Integer Int32)) in
      call ~result:(Lowered.make_local_place order) Compare_bytes
        [
          Copy (Storage.project_buffer left);
          Copy (Storage.project_buffer right);
          Copy (Lowered.make_local_place count);
        ];
      Emit_c.Ir_builder.emit_when builder
        (Test (Equal, Copy (Lowered.make_local_place order), Constant (Integer (Int32, Z.zero))))
        (fun () ->
          let emit_int32 rvalue =
            Emit_c.Ir_builder.emit_temporary builder (Raw (Integer Int32)) rvalue
          in
          let longer = emit_bool (Compare (Greater, copy_length left, copy_length right)) in
          let shorter = emit_bool (Compare (Less, copy_length left, copy_length right)) in
          let first = emit_int32 (Convert (longer, Integer Int32)) in
          let second = emit_int32 (Convert (shorter, Integer Int32)) in
          Emit_c.Ir_builder.emit builder
            (Assign (Lowered.make_local_place order, Binary (Subtract, first, second))));
      set (Convert (Copy (Lowered.make_local_place order), Integer Int8))
  | Storage_empty -> set (Storage.build_empty (Storage.make_storage_type (read_element_type ())))
  | Storage_with_capacity ->
      let ty = Storage.make_storage_type (read_element_type ()) in
      let result = Emit_c.Ir_builder.allocate_local builder (Value ty) in
      Emit_c.Ir_builder.emit builder
        (Assign (Lowered.make_local_place result, Storage.build_empty ty));
      Emit_c.Ir_builder.emit_when builder
        (Test (Greater, read_operand 0, Lowered.make_uint64_constant 0))
        (fun () -> resize_buffer (Lowered.make_local_place result) (read_operand 0));
      set (Use (Move (Lowered.make_local_place result)))
  | Storage_length | View_length -> set (Use (copy_length (extract_place (read_argument 0))))
  | Storage_capacity ->
      set (Use (Copy (Storage.project_capacity (extract_place (read_argument 0)))))
  | Storage_set_capacity ->
      let storage = extract_place (read_argument 0) in
      fail_obligation_when
        (Test (Less, read_operand 1, copy_length storage))
        "a storage's capacity set to less than its length";
      Emit_c.Ir_builder.emit_if builder
        (Test (Greater, read_operand 1, Lowered.make_uint64_constant 0))
        ~yes:(fun () -> resize_buffer storage (read_operand 1))
        ~no:(fun () ->
          Emit_c.Ir_builder.emit builder (Drop storage);
          Emit_c.Ir_builder.emit builder
            (Assign (storage, Storage.build_empty (Storage.make_storage_type (read_element_type ())))))
  | Storage_lengthen ->
      let storage = extract_place (read_argument 0) in
      fail_obligation_when
        (Test (Greater, read_operand 1, compute_room storage))
        "a storage lengthened to more than its capacity";
      add_to_length storage (read_operand 1)
  | Storage_shorten ->
      let storage = extract_place (read_argument 0) in
      fail_obligation_when
        (Test (Greater, read_operand 1, copy_length storage))
        "a storage shortened to more than its length";
      Emit_c.Ir_builder.emit builder (Assign (Storage.project_length storage, Use (read_operand 1)))
  | Storage_push ->
      let storage = extract_place (read_argument 0) in
      fail_obligation_when
        (Test (Greater_equal, copy_length storage, Copy (Storage.project_capacity storage)))
        "an element pushed to a storage that has no room";
      Emit_c.Ir_builder.emit builder
        (Assign (index_element storage (copy_length storage), Use (read_operand 1)));
      add_to_length storage (Lowered.make_uint64_constant 1)
  | Storage_pop ->
      let storage = extract_place (read_argument 0) in
      fail_obligation_when
        (Test (Equal, copy_length storage, Lowered.make_uint64_constant 0))
        "an element popped from an empty storage";
      Emit_c.Ir_builder.emit builder
        (Assign
           ( Storage.project_length storage,
             Binary (Subtract, copy_length storage, Lowered.make_uint64_constant 1) ));
      set (Use (Move (index_element storage (copy_length storage))))
  | Storage_insert ->
      let storage = extract_place (read_argument 0) in
      let index = read_operand 1 in
      fail_obligation_when (Test (Greater, index, copy_length storage)) "index out of bounds";
      fail_obligation_when
        (Test (Greater_equal, copy_length storage, Copy (Storage.project_capacity storage)))
        "an element inserted into a storage that has no room";
      let after = emit_uint64 (Binary (Add, index, Lowered.make_uint64_constant 1)) in
      let tail_length = emit_uint64 (Binary (Subtract, copy_length storage, index)) in
      let bytes = emit_uint64 (Binary (Multiply, tail_length, element_size ())) in
      call Move_bytes
        [
          Address { place = index_element storage after; writable = true };
          Address { place = index_element storage index; writable = true };
          bytes;
        ];
      Emit_c.Ir_builder.emit builder (Assign (index_element storage index, Use (read_operand 2)));
      add_to_length storage (Lowered.make_uint64_constant 1)
  | Storage_remove ->
      check_index (read_operand 1) (copy_length (extract_place (read_argument 0)));
      let storage = extract_place (read_argument 0) in
      let index = read_operand 1 in
      set (Use (Move (index_element storage index)));
      let after = emit_uint64 (Binary (Add, index, Lowered.make_uint64_constant 1)) in
      let tail_length = emit_uint64 (Binary (Subtract, copy_length storage, after)) in
      let bytes = emit_uint64 (Binary (Multiply, tail_length, element_size ())) in
      call Move_bytes
        [
          Address { place = index_element storage index; writable = true };
          Address { place = index_element storage after; writable = true };
          bytes;
        ];
      Emit_c.Ir_builder.emit builder
        (Assign
           ( Storage.project_length storage,
             Binary (Subtract, copy_length storage, Lowered.make_uint64_constant 1) ))
  | Storage_from_array ->
      let count = read_array_length () in
      let array_ty = make_array_type count in
      let ty = Storage.make_storage_type (read_element_type ()) in
      let result = Emit_c.Ir_builder.allocate_local builder (Value ty) in
      Emit_c.Ir_builder.emit builder
        (Assign (Lowered.make_local_place result, Storage.build_empty ty));
      if Z.sign count > 0 then
        resize_buffer (Lowered.make_local_place result) (Constant (Integer (UInt64, count)));
      if Z.sign count > 0 && (Memory_layout.of_type env array_ty).size > 0 then begin
        let untyped = Emit_c.Ir_builder.allocate_local builder (Raw (Pointer Opaque)) in
        Emit_c.Ir_builder.emit builder
          (Assign
             ( Lowered.make_local_place untyped,
               Use (Copy (Storage.project_buffer (Lowered.make_local_place result))) ));
        let typed =
          Emit_c.Ir_builder.allocate_local builder
            (Pointer { target = Value array_ty; writable = true })
        in
        Emit_c.Ir_builder.emit builder
          (Assign (Lowered.make_local_place typed, Use (Copy (Lowered.make_local_place untyped))));
        Emit_c.Ir_builder.emit builder
          (Assign ({ root = Local typed; projections = [ Deref ] }, Use (read_operand 0)))
      end;
      add_to_length (Lowered.make_local_place result) (Constant (Integer (UInt64, count)));
      set (Use (Move (Lowered.make_local_place result)))
  | Array_from_storage ->
      let count = read_array_length () in
      let array_ty = make_array_type count in
      let moved_storage =
        Lowered.make_local_place
          (Emit_c.Ir_builder.allocate_local builder
             (Value (Storage.make_storage_type (read_element_type ()))))
      in
      Emit_c.Ir_builder.emit builder
        (Assign (moved_storage, Use (Move (extract_place (read_argument 0)))));
      fail_obligation_when
        (Test (Not_equal, copy_length moved_storage, Constant (Integer (UInt64, count))))
        "a storage made into an array of another length";
      if Z.sign count > 0 && (Memory_layout.of_type env array_ty).size > 0 then begin
        let untyped = Emit_c.Ir_builder.allocate_local builder (Raw (Pointer Opaque)) in
        Emit_c.Ir_builder.emit builder
          (Assign
             (Lowered.make_local_place untyped, Use (Copy (Storage.project_buffer moved_storage))));
        let typed =
          Emit_c.Ir_builder.allocate_local builder
            (Pointer { target = Value array_ty; writable = true })
        in
        Emit_c.Ir_builder.emit builder
          (Assign (Lowered.make_local_place typed, Use (Copy (Lowered.make_local_place untyped))));
        set (Use (Move { root = Local typed; projections = [ Deref ] }))
      end;
      Emit_c.Ir_builder.emit_when builder
        (Test (Storage.make_owned_block_test moved_storage))
        (fun () -> call Free [ Copy (Storage.project_buffer moved_storage) ])
  | Array_view ->
      let count = read_array_length () in
      let array_ty = make_array_type count in
      let elements : Lowered.operand =
        if Memory_layout.has_zero_size env array_ty then Constant Storage.empty_buffer
        else
          Address
            {
              place =
                Lowered.project (read (read_argument 0)) (Index (Lowered.make_uint64_constant 0));
              writable = false;
            }
      in
      set
        (Storage.build_view
           (Storage.make_view_type (read_element_type ()))
           ~buffer:elements
           ~length:(Constant (Integer (UInt64, count))))
  | Storage_swap | View_swap ->
      check_index (read_operand 1) (copy_length (extract_place (read_argument 0)));
      check_index (read_operand 2) (copy_length (extract_place (read_argument 0)));
      let index_element index = Storage.index_element (extract_place (read_argument 0)) index in
      let held = Emit_c.Ir_builder.allocate_local builder (Value (read_element_type ())) in
      Emit_c.Ir_builder.emit builder
        (Assign (Lowered.make_local_place held, Use (Move (index_element (read_operand 1)))));
      Emit_c.Ir_builder.emit builder
        (Assign (index_element (read_operand 1), Use (Move (index_element (read_operand 2)))));
      Emit_c.Ir_builder.emit builder
        (Assign (index_element (read_operand 2), Use (Move (Lowered.make_local_place held))))
  | Storage_view ->
      let storage = extract_place (read_argument 0) in
      set
        (Storage.build_view
           (Storage.make_view_type (read_element_type ()))
           ~buffer:(Copy (Storage.project_buffer storage))
           ~length:(copy_length storage))
  | View_address ->
      set
        (Convert (Copy (Storage.project_buffer (extract_place (read_argument 0))), Integer UInt64))
  | View_slice ->
      let view = extract_place (read_argument 0) in
      fail_obligation_when (Test (Greater, read_operand 1, read_operand 2)) "slice out of bounds";
      fail_obligation_when (Test (Greater, read_operand 2, copy_length view)) "slice out of bounds";
      let count = emit_uint64 (Binary (Subtract, read_operand 2, read_operand 1)) in
      set
        (Storage.build_view
           (Storage.make_view_type (read_element_type ()))
           ~buffer:
             (Address { place = Storage.index_element view (read_operand 1); writable = false })
           ~length:count)
  | Storage_model | View_model | Array_model ->
      raise_bug "a model, which exists only in specifications"

let lower_lend (context : Context.t) (lend : Intrinsic.lend) : Lowered.place =
  let read_argument = Context.read_argument context in
  let read_operand = Context.read_operand context in
  let check_index = Context.check_index context in
  let read_array_length () = Context.read_array_length context in
  let copy_length = Context.copy_length in
  let index_element = Storage.index_element in
  let extract_place = Context.extract_place in
  match lend with
  | Storage_at | Storage_at_mut | View_at | View_at_mut ->
      let sequence = extract_place (read_argument 0) in
      check_index (read_operand 1) (copy_length sequence);
      index_element sequence (read_operand 1)
  | Array_at_mut ->
      check_index (read_operand 1) (Constant (Integer (UInt64, read_array_length ())));
      Lowered.project (extract_place (read_argument 0)) (Index (read_operand 1))
