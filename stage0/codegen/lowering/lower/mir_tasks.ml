let make_tasks_call (state : Lowering.state) method_ ?result (places : Lowered.place list) :
    Lowered.statement =
  let { Well_known.owner; name; _ } = Well_known.locate_method method_ in
  let capability = Well_known.make_path owner in
  let slot, signature = Targets.lookup_capability_method state.context capability name in
  let c_signature, convention = Targets.make_entry_signature state.context signature in
  Call
    {
      target =
        Evidence_call
          {
            evidence = Targets.lookup_evidence state capability;
            capability;
            slot;
            signature = c_signature;
          };
      arguments =
        List.filter_map Fun.id
          (List.map2
             (fun (mode, ty) place ->
               Targets.pass state mode
                 (Monomorphic.ground state.context.monomorphic Types.no_substitution ty)
                 place)
             (Definitions.list_interface_parameters { signature with receiver = None })
             places);
      result =
        (match result with
        | Some place -> Convention.make_destination convention place
        | None -> Discarded);
    }

let call_tasks_bool (state : Lowering.state) method_ places : Lowered.operand =
  let result =
    Lowered.make_local_place
      (Emit_c.Ir_builder.allocate_local state.builder (Value state.context.bool))
  in
  Emit_c.Ir_builder.emit state.builder (make_tasks_call state method_ ~result places);
  Copy result

let with_group state (f : Lowered.place -> unit) =
  let scope = Lowering.open_scope state Statement in
  let group =
    Lowered.make_local_place
      (Emit_c.Ir_builder.allocate_local state.builder (Value (Ground.make_builtin UInt64)))
  in
  Emit_c.Ir_builder.emit state.builder (make_tasks_call state Tasks_open ~result:group []);
  let join = make_tasks_call state Tasks_join [ group ] in
  let cleanup = Lowering.Join_group join in
  scope.owned <- [ cleanup ];
  f group;
  Emit_c.Ir_builder.emit state.builder join;
  scope.owned <- List.filter (fun owned -> owned != cleanup) scope.owned;
  Lowering.close_scope state scope

let compute_task_function_type (state : Lowering.state) : Lowered.ty =
  let { Well_known.owner; name; _ } = Well_known.locate_method Tasks_spawn in
  let _, signature =
    Targets.lookup_capability_method state.context (Well_known.make_path owner) name
  in
  match signature.parameters with
  | [ _; work; _ ] ->
      Value (Monomorphic.ground state.context.monomorphic Types.no_substitution work.type_)
  | _ -> Definitions.raise_bug "Tasks.spawn does not take a group, a function, and an item"

let lower_task_body (state : Lowering.state) ~(id : Mir.task) ~group ~parts
    (f : Lowering.task -> unit) : Lowered.rvalue =
  let capabilities = Emit_c.Ir_builder.allocate_local state.builder Convention.capabilities in
  let nested, environment =
    Lowering.outline state ~parts:(parts @ [ capabilities ]) (fun () ->
        let task =
          {
            Lowering.id;
            group;
            end_block = Emit_c.Ir_builder.allocate_block state.builder;
            scope_depth = List.length state.scopes;
          }
        in
        state.tasks <- task :: state.tasks;
        f task;
        state.tasks <- List.tl state.tasks;
        Emit_c.Ir_builder.finish state.builder (Goto task.end_block);
        Emit_c.Ir_builder.start state.builder task.end_block;
        Emit_c.Ir_builder.finish state.builder (Return None))
  in
  Function_value { code = Nested nested; environment = Some environment }

let lock_evidence (state : Lowering.state) ~(tasks : Lowered.operand)
    (evidence : (Path.t * Lowered.operand) list) =
  let mutex =
    Lowered.make_local_place
      (Emit_c.Ir_builder.allocate_local state.builder (Value (Ground.make_builtin UInt64)))
  in
  Emit_c.Ir_builder.emit state.builder
    (Assign (mutex, Use (Lowering.make_int_constant UInt64 Z.zero)));
  List.map
    (fun (capability, implementation) ->
      let slot = Emit_c.Ir_builder.allocate_local state.builder (Evidence 2) in
      Emit_c.Ir_builder.emit state.builder
        (Call
           {
             target = Intrinsic Evidence_fill;
             arguments =
               [
                 Address { place = Lowered.make_local_place slot; writable = true };
                 Address { place = mutex; writable = true };
                 Constant (Symbol_address (Table (Locked_table capability)));
                 implementation;
                 tasks;
               ];
             result = Discarded;
           });
      (capability, Lowered.Address { place = Lowered.make_local_place slot; writable = false }))
    evidence

let cancel (state : Lowering.state) ~(task : Mir.task) ~winner ~number ~value =
  match state.tasks with
  | current :: _ when current.id = task ->
      let won = Emit_c.Ir_builder.allocate_block state.builder
      and lost = Emit_c.Ir_builder.allocate_block state.builder
      and after = Emit_c.Ir_builder.allocate_block state.builder in
      Emit_c.Ir_builder.branch state.builder
        (Holds (call_tasks_bool state Tasks_cancel [ current.group ]))
        ~yes:won ~no:lost;
      Emit_c.Ir_builder.start state.builder won;
      Emit_c.Ir_builder.emit state.builder
        (Assign
           ( Mir_places.lookup_local_place state winner,
             Use (Lowering.make_int_constant UInt32 (Z.of_int number)) ));
      Option.iter
        (fun (value, ty, slot) ->
          Emit_c.Ir_builder.emit state.builder
            (Assign
               ( Mir_places.lookup_local_place state slot,
                 Use (Lowering.make_owned_operand state value ty) )))
        value;
      Emit_c.Ir_builder.finish state.builder (Goto after);
      Emit_c.Ir_builder.start state.builder lost;
      Option.iter
        (fun (value, ty, _) ->
          if not (Lowering.is_trivial state ty) then
            Emit_c.Ir_builder.emit state.builder (Drop value))
        value;
      Emit_c.Ir_builder.finish state.builder (Goto after);
      Emit_c.Ir_builder.start state.builder after;
      Lowering.leave_to state current.scope_depth;
      Emit_c.Ir_builder.finish state.builder (Goto current.end_block);
      Emit_c.Ir_builder.start state.builder (Emit_c.Ir_builder.allocate_block state.builder)
  | _ ->
      Definitions.raise_bug "an early exit leaves a task that is not the innermost enclosing task"

let spawn_iteration (state : Lowering.state) (loop : Lowering.spawn_loop)
    ~(on_not_spawned : unit -> unit) (f : unit -> unit) =
  let function_value =
    Emit_c.Ir_builder.allocate_local state.builder (compute_task_function_type state)
  in
  Emit_c.Ir_builder.emit state.builder
    (Assign
       ( Lowered.make_local_place function_value,
         lower_task_body state
           ~id:(Iteration { loop = loop.origin })
           ~group:loop.group ~parts:[ loop.item ]
           (fun task ->
             Lowering.run_in_loop state ~continue_:task.end_block ~break_:task.end_block
               ~depth:task.scope_depth f) ));
  let spawned =
    call_tasks_bool state Tasks_spawn
      [ loop.group; Lowered.make_local_place function_value; Lowered.make_local_place loop.item ]
  in
  let next = Emit_c.Ir_builder.allocate_block state.builder
  and cancelled = Emit_c.Ir_builder.allocate_block state.builder in
  Emit_c.Ir_builder.branch state.builder (Holds spawned) ~yes:next ~no:cancelled;
  Emit_c.Ir_builder.start state.builder cancelled;
  on_not_spawned ();
  Mir_drops.break_loop state;
  Emit_c.Ir_builder.start state.builder next

let spawn_with_item state (loop : Lowering.spawn_loop) (value : Lowered.place) ~owned:is_owned
    ~(each : Lowered.place -> unit) =
  let ty = loop.element in
  let item = Lowered.make_local_place loop.item in
  let boxed = not (Lowering.is_zero_size state ty) in
  let move_or_copy place : Lowered.operand =
    if is_owned then Lowering.make_owned_operand state place ty else Copy place
  in
  let allocate_block () : Lowered.local * Lowered.place =
    let pointer = Emit_c.Ir_builder.allocate_local state.builder (Raw (Pointer Opaque)) in
    Emit_c.Ir_builder.emit state.builder
      (Assign (Lowered.make_local_place pointer, Convert (Copy item, Pointer Opaque)));
    let typed =
      Emit_c.Ir_builder.allocate_local state.builder
        (Pointer { target = Value ty; writable = true })
    in
    Emit_c.Ir_builder.emit state.builder
      (Assign (Lowered.make_local_place typed, Use (Copy (Lowered.make_local_place pointer))));
    (pointer, { root = Local typed; projections = [ Deref ] })
  in
  let unbox ~dropped_here : Lowered.place =
    if boxed then begin
      let unboxed =
        if is_owned && dropped_here then Lowering.allocate_binding state ty
        else Lowered.make_local_place (Emit_c.Ir_builder.allocate_local state.builder (Value ty))
      in
      let pointer, inside = allocate_block () in
      Emit_c.Ir_builder.emit state.builder (Assign (unboxed, Use (move_or_copy inside)));
      Emit_c.Ir_builder.emit state.builder
        (Call
           {
             target = Intrinsic Free;
             arguments = [ Copy (Lowered.make_local_place pointer) ];
             result = Discarded;
           });
      unboxed
    end
    else Lowered.make_local_place (Emit_c.Ir_builder.allocate_local state.builder (Value ty))
  in
  if boxed then begin
    let pointer = Emit_c.Ir_builder.allocate_local state.builder (Raw (Pointer Opaque)) in
    Emit_c.Ir_builder.emit state.builder
      (Call
         {
           target = Intrinsic Allocate;
           arguments = [ Constant (Size_of ty); Constant (Alignment_of ty) ];
           result = Returned (Lowered.make_local_place pointer);
         });
    Emit_c.Ir_builder.emit state.builder
      (Assign (item, Convert (Copy (Lowered.make_local_place pointer), Integer UInt64)));
    Emit_c.Ir_builder.emit state.builder
      (Assign (snd (allocate_block ()), Use (move_or_copy value)))
  end
  else
    Emit_c.Ir_builder.emit state.builder
      (Assign (item, Use (Lowering.make_int_constant UInt64 Z.zero)));
  spawn_iteration state loop
    ~on_not_spawned:(fun () ->
      Lowering.run_in_scope state (fun () -> ignore (unbox ~dropped_here:true)))
    (fun () -> Lowering.run_in_scope state (fun () -> each (unbox ~dropped_here:false)))
