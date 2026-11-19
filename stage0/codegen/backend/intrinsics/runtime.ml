let raise_bug format = Context.raise_bug format

let lower (context : Context.t) (runtime : Intrinsic.runtime) =
  let builder = context.builder in
  let env = context.env in
  let types = context.types in
  let destination = context.destination in
  let site = context.site in
  let reported = context.reported in
  let trace = context.trace in
  let set = Context.set context in
  let read_argument = Context.read_argument context in
  let read_operand = Context.read_operand context in
  let read_type_argument = Context.read_type_argument context in
  let call = Context.call context in
  let allocate_uint64_local () = Context.allocate_uint64_local context in
  let extract_place = Context.extract_place in
  let read = Context.read in
  let byte = Ground.make_builtin UInt8 in
  match runtime with
  | Crash ->
      let message = read (read_argument 0) in
      let bytes =
        match (Memory_layout.of_type env types.string_slice).form with
        | Struct [ only ] -> Lowered.project message (Field only.name)
        | _ -> raise_bug "a StringSlice that is not a record of one field"
      in
      Emit_c.Ir_builder.finish builder
        (Fail
           {
             failure = Panic;
             message = Copy (Storage.project_buffer bytes);
             length = Copy (Storage.project_length bytes);
             site;
             reported;
             trace;
           });
      Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder)
  | Handle_from ->
      set
        (Build
           {
             ty = Ground.make_builtin Handle;
             variant = None;
             fields = [ ("descriptor", read_operand 0) ];
           })
  | Handle_descriptor ->
      set (Use (Copy (Lowered.project (read (read_argument 0)) (Field "descriptor"))))
  | Shared_new ->
      let ty = read_type_argument 0 in
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
          (Assign ({ root = Local typed; projections = [ Deref ] }, Use (read_operand 0)))
      end;
      set
        (Build
           {
             ty = Ground.make_builtin Shared ~arguments:[ Type ty ];
             variant = None;
             fields = [ ("value", Copy (Lowered.make_local_place block)) ];
           })
  | Shared_key ->
      set
        (Convert (Copy (Lowered.project (read (read_argument 0)) (Field "value")), Integer UInt64))
  | Shared_update -> raise_bug "shared_update is lowered with the call of its function value"
  | Holds_invariant -> raise_bug "holds_invariant is lowered with its type's invariant"
  | Handle_release ->
      let released =
        Emit_c.Ir_builder.allocate_local builder (Value (Ground.make_builtin Handle))
      in
      Emit_c.Ir_builder.emit builder
        (Assign (Lowered.make_local_place released, Use (read_operand 0)));
      set (Use (Copy (Lowered.project (Lowered.make_local_place released) (Field "descriptor"))))
  | Run_test -> call Run_test [ read_operand 0 ]
  | Coroutine_start ->
      call ?result:destination Coroutine_start [ Copy (read (read_argument 0)); read_operand 1 ]
  | Coroutine_resume -> call ?result:destination Coroutine_resume [ read_operand 0 ]
  | Coroutine_suspend -> call Coroutine_suspend []
  | Tasks_spawn ->
      call ?result:destination Tasks_spawn
        [ read_operand 0; Copy (read (read_argument 1)); read_operand 2 ]
  | Report_tests_to -> call Report_tests_to [ read_operand 0 ]
  | Live_blocks -> call ?result:destination Live_blocks []
  | System_is_os os -> set (Use (Constant (Bool ((Memory_layout.system env).os = os))))
  | System_is_architecture architecture ->
      set (Use (Constant (Bool ((Memory_layout.system env).architecture = architecture))))
  | Environment_entry ->
      let environment = Emit_c.Ir_builder.allocate_local builder (Raw (Pointer Opaque)) in
      call ~result:(Lowered.make_local_place environment) Environment [];
      let position = allocate_uint64_local () in
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
      Libc_calls.load_text_at context entry ~is_present:(extract_place (read_argument 1))
  | Libc function_ -> Libc_calls.lower context function_
  | Libc_number number -> set (Use (Libc_calls.make_number_constant context number))
