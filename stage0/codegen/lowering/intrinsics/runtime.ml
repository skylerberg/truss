let lower (context : Context.t) (runtime : Intrinsic.runtime) =
  let builder = context.builder in
  let env = context.env in
  let destination = context.destination in
  let set = Context.set context in
  let read_argument = Context.read_argument context in
  let read_operand = Context.read_operand context in
  let call = Context.call context in
  let byte = Ground.make_builtin UInt8 in
  match runtime with
  | Crash ->
      let message = Context.read (read_argument 0) in
      let bytes =
        match (Memory_layout.of_type env context.types.string_slice).form with
        | Struct [ only ] -> Lowered.project message (Field only.name)
        | _ -> Context.raise_bug "a StringSlice that is not a record of one field"
      in
      Context.panic_with_message context
        ~message:(Copy (Storage.project_buffer bytes))
        ~length:(Copy (Storage.project_length bytes));
      Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder)
  | Handle_from -> set (Builtin_records.Handle.build ~descriptor:(read_operand 0))
  | Handle_descriptor ->
      set (Use (Copy (Builtin_records.Handle.project_descriptor (Context.read (read_argument 0)))))
  | Shared_new ->
      let ty = Context.read_type_argument context 0 in
      let block = Emit_c.Ir_builder.allocate_local builder (Raw (Pointer Opaque)) in
      call ~result:(Lowered.make_local_place block) Shared_allocate
        [ Constant (Size_of ty); Constant (Alignment_of ty) ];
      if (Memory_layout.of_type env ty).size > 0 then begin
        let typed =
          Emit_c.Ir_builder.allocate_local builder (Pointer { target = Value ty; writable = true })
        in
        Emit_c.Ir_builder.emit builder
          (Assign (Lowered.make_local_place typed, Use (Copy (Lowered.make_local_place block))));
        Emit_c.Ir_builder.emit builder
          (Assign (Lowered.make_deref_place typed, Use (read_operand 0)))
      end;
      set (Builtin_records.Shared.build ty ~value:(Copy (Lowered.make_local_place block)))
  | Shared_key ->
      set
        (Convert
           ( Copy (Builtin_records.Shared.project_value (Context.read (read_argument 0))),
             Integer UInt64 ))
  | Shared_update ->
      Context.raise_bug "shared_update is lowered with the call of its function value"
  | Holds_invariant -> Context.raise_bug "holds_invariant is lowered with its type's invariant"
  | Handle_release ->
      let released =
        Emit_c.Ir_builder.allocate_local builder (Value (Ground.make_builtin Handle))
      in
      Emit_c.Ir_builder.emit builder
        (Assign (Lowered.make_local_place released, Use (read_operand 0)));
      set
        (Use (Copy (Builtin_records.Handle.project_descriptor (Lowered.make_local_place released))))
  | Run_test -> call Run_test [ read_operand 0 ]
  | Coroutine_start ->
      let body = Context.read (read_argument 0) in
      call ?result:destination Coroutine_start
        [
          Copy (Builtin_records.Function_value.project_code body);
          Copy (Builtin_records.Function_value.project_environment body);
          read_operand 1;
        ]
  | Coroutine_resume -> call ?result:destination Coroutine_resume [ read_operand 0 ]
  | Coroutine_suspend -> call Coroutine_suspend []
  | Tasks_spawn ->
      let work = Context.read (read_argument 1) in
      call ?result:destination Tasks_spawn
        [
          read_operand 0;
          Copy (Builtin_records.Function_value.project_code work);
          Copy (Builtin_records.Function_value.project_environment work);
          read_operand 2;
        ]
  | Report_tests_to -> call Report_tests_to [ read_operand 0 ]
  | Live_blocks -> call ?result:destination Live_blocks []
  | System_is_os os -> set (Use (Constant (Bool ((Memory_layout.system env).os = os))))
  | System_is_architecture architecture ->
      set (Use (Constant (Bool ((Memory_layout.system env).architecture = architecture))))
  | Environment_entry ->
      let environment = Emit_c.Ir_builder.allocate_local builder (Raw (Pointer Opaque)) in
      call ~result:(Lowered.make_local_place environment) Environment [];
      let position = Context.allocate_uint64_local context in
      Emit_c.Ir_builder.emit builder
        (Assign (Lowered.make_local_place position, Use (Lowered.make_uint64_constant 0)));
      let entry = Emit_c.Ir_builder.allocate_local builder (Raw (Nullable_pointer (Data byte))) in
      let test = Emit_c.Ir_builder.allocate_block builder
      and next = Emit_c.Ir_builder.allocate_block builder
      and after = Emit_c.Ir_builder.allocate_block builder in
      Emit_c.Ir_builder.finish builder (Goto test);
      Emit_c.Ir_builder.start builder test;
      call ~result:(Lowered.make_local_place entry) Program_argument
        [ Copy (Lowered.make_local_place environment); Copy (Lowered.make_local_place position) ];
      Emit_c.Ir_builder.branch builder
        (Disjunction
           ( Test (Equal, Copy (Lowered.make_local_place entry), Constant Null),
             Test (Equal, Copy (Lowered.make_local_place position), read_operand 0) ))
        ~yes:after ~no:next;
      Emit_c.Ir_builder.start builder next;
      Emit_c.Ir_builder.emit builder
        (Assign
           ( Lowered.make_local_place position,
             Binary (Add, Copy (Lowered.make_local_place position), Lowered.make_uint64_constant 1)
           ));
      Emit_c.Ir_builder.finish builder (Goto test);
      Emit_c.Ir_builder.start builder after;
      Libc_calls.load_text_at context entry ~is_present:(Context.read_place context 1)
  | Libc function_ -> Libc_calls.lower context function_
  | Libc_number number -> set (Use (Libc_calls.make_number_constant context number))
