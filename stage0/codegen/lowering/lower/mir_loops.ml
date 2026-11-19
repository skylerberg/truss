let lower_range_loop state ~(schedule : Lowering.schedule) ~(low : Mir.operand)
    ~(high : Mir.operand) ~inclusive ~each =
  let element = Mir_places.compute_operand_type state low in
  let scalar = Lowering.classify_scalar state element in
  let make_constant value : Lowered.operand =
    match scalar with
    | Integer integer -> Lowering.make_int_constant integer (Z.of_int value)
    | Character -> Constant (Character value)
    | _ -> Definitions.raise_bug "a range of %s" (Ground.to_string element)
  in
  let characters = scalar = Character in
  let compare op left right : Emit_c.Ir_builder.condition = Test (op, left, right) in
  match schedule with
  | Chunked ->
      let wide = Lowered.Raw (Integer UInt64) in
      let one = Lowering.make_int_constant UInt64 Z.one in
      let first_value = Lowering.allocate_binding state element in
      let last_value = Lowering.allocate_binding state element in
      Emit_c.Ir_builder.emit state.builder
        (Assign (first_value, Use (Mir_places.lower_operand state low)));
      Emit_c.Ir_builder.emit state.builder
        (Assign (last_value, Use (Mir_places.lower_operand state high)));
      let inside = Emit_c.Ir_builder.allocate_block state.builder
      and after = Emit_c.Ir_builder.allocate_block state.builder in
      let depth = List.length state.scopes in
      Emit_c.Ir_builder.branch state.builder
        (Test ((if inclusive then Less_equal else Less), Copy first_value, Copy last_value))
        ~yes:inside ~no:after;
      Emit_c.Ir_builder.start state.builder inside;
      let first = Emit_c.Ir_builder.allocate_local state.builder wide
      and last = Emit_c.Ir_builder.allocate_local state.builder wide in
      Emit_c.Ir_builder.emit state.builder
        (Assign (Lowered.make_local_place first, Use (Lowering.make_int_constant UInt64 Z.zero)));
      let low_wide =
        Emit_c.Ir_builder.emit_value state.builder wide (Convert (Copy first_value, Integer UInt64))
      in
      let high_wide =
        Emit_c.Ir_builder.emit_value state.builder wide (Convert (Copy last_value, Integer UInt64))
      in
      Emit_c.Ir_builder.emit state.builder
        (Assign (Lowered.make_local_place last, Binary (Subtract, high_wide, low_wide)));
      if not inclusive then
        Emit_c.Ir_builder.emit state.builder
          (Assign
             ( Lowered.make_local_place last,
               Binary (Subtract, Copy (Lowered.make_local_place last), one) ));
      if characters then
        Emit_c.Ir_builder.emit_when state.builder
          (Conjunction
             ( compare Less (Copy first_value) (make_constant 0xD800),
               compare Greater (Copy last_value) (make_constant 0xDFFF) ))
          (fun () ->
            Emit_c.Ir_builder.emit state.builder
              (Assign
                 ( Lowered.make_local_place last,
                   Binary
                     ( Subtract,
                       Copy (Lowered.make_local_place last),
                       Lowering.make_int_constant UInt64 (Z.of_int 0x800) ) )));
      let body, environment =
        Lowering.outline state ~parts:[ first; last ] (fun () ->
            let index = Emit_c.Ir_builder.allocate_local state.builder wide in
            Emit_c.Ir_builder.emit state.builder
              (Assign (Lowered.make_local_place index, Use (Copy (Lowered.make_local_place first))));
            let again = Emit_c.Ir_builder.allocate_block state.builder
            and step = Emit_c.Ir_builder.allocate_block state.builder
            and done_ = Emit_c.Ir_builder.allocate_block state.builder in
            Emit_c.Ir_builder.finish state.builder (Goto again);
            Emit_c.Ir_builder.start state.builder again;
            Lowering.run_in_scope state (fun () ->
                let offset = Lowering.allocate_binding state element in
                let bound = Lowering.allocate_binding state element in
                Emit_c.Ir_builder.emit state.builder
                  (Assign (offset, Convert (Copy (Lowered.make_local_place index), scalar)));
                Emit_c.Ir_builder.emit state.builder
                  (Assign (bound, Binary (Add, Copy first_value, Copy offset)));
                if characters then
                  Emit_c.Ir_builder.emit_when state.builder
                    (Conjunction
                       ( compare Less (Copy first_value) (make_constant 0xD800),
                         compare Greater_equal (Copy bound) (make_constant 0xD800) ))
                    (fun () ->
                      Emit_c.Ir_builder.emit state.builder
                        (Assign (bound, Binary (Add, Copy bound, make_constant 0x800))));
                Lowering.run_in_loop state ~continue_:step ~break_:done_ ~depth (fun () ->
                    each bound));
            Emit_c.Ir_builder.finish state.builder (Goto step);
            Emit_c.Ir_builder.start state.builder step;
            let next = Emit_c.Ir_builder.allocate_block state.builder in
            Emit_c.Ir_builder.branch state.builder
              (Test
                 (Equal, Copy (Lowered.make_local_place index), Copy (Lowered.make_local_place last)))
              ~yes:done_ ~no:next;
            Emit_c.Ir_builder.start state.builder next;
            Emit_c.Ir_builder.emit state.builder
              (Assign
                 ( Lowered.make_local_place index,
                   Binary (Add, Copy (Lowered.make_local_place index), one) ));
            Emit_c.Ir_builder.finish state.builder (Goto again);
            Emit_c.Ir_builder.start state.builder done_;
            Emit_c.Ir_builder.finish state.builder (Return None))
      in
      Emit_c.Ir_builder.emit state.builder
        (Fork_range
           {
             body;
             environment;
             first = Copy (Lowered.make_local_place first);
             last = Copy (Lowered.make_local_place last);
           });
      Emit_c.Ir_builder.finish state.builder (Goto after);
      Emit_c.Ir_builder.start state.builder after
  | Sequential | Spawned _ ->
      let allocate_loop_value () = Lowering.allocate_binding state element in
      let index = allocate_loop_value () in
      let stop = allocate_loop_value () in
      Emit_c.Ir_builder.emit state.builder
        (Assign (index, Use (Mir_places.lower_operand state low)));
      Emit_c.Ir_builder.emit state.builder
        (Assign (stop, Use (Mir_places.lower_operand state high)));
      let test = Emit_c.Ir_builder.allocate_block state.builder
      and inside = Emit_c.Ir_builder.allocate_block state.builder
      and step = Emit_c.Ir_builder.allocate_block state.builder
      and after = Emit_c.Ir_builder.allocate_block state.builder in
      let depth = List.length state.scopes in
      Emit_c.Ir_builder.finish state.builder (Goto test);
      Emit_c.Ir_builder.start state.builder test;
      Emit_c.Ir_builder.branch state.builder
        (Test ((if inclusive then Less_equal else Less), Copy index, Copy stop))
        ~yes:inside ~no:after;
      Emit_c.Ir_builder.start state.builder inside;
      Lowering.run_in_loop state ~continue_:step ~break_:after ~depth (fun () ->
          let run value =
            Lowering.run_in_scope state (fun () ->
                let bound = allocate_loop_value () in
                Emit_c.Ir_builder.emit state.builder (Assign (bound, value));
                each bound)
          in
          match schedule with
          | Spawned loop ->
              let item = Lowered.make_local_place loop.item in
              Emit_c.Ir_builder.emit state.builder
                (Assign (item, Convert (Copy index, Integer UInt64)));
              Mir_tasks.spawn_iteration state loop ~on_not_spawned:ignore (fun () ->
                  run (Convert (Copy item, scalar)))
          | Sequential | Chunked -> run (Use (Copy index)));
      Emit_c.Ir_builder.finish state.builder (Goto step);
      Emit_c.Ir_builder.start state.builder step;
      if inclusive then begin
        let next = Emit_c.Ir_builder.allocate_block state.builder in
        Emit_c.Ir_builder.branch state.builder
          (Test (Equal, Copy index, Copy stop))
          ~yes:after ~no:next;
        Emit_c.Ir_builder.start state.builder next
      end;
      Emit_c.Ir_builder.emit state.builder
        (Assign (index, Binary (Add, Copy index, make_constant 1)));
      if characters then
        Emit_c.Ir_builder.emit_when state.builder
          (Test (Equal, Copy index, make_constant 0xD800))
          (fun () ->
            Emit_c.Ir_builder.emit state.builder (Assign (index, Use (make_constant 0xE000))));
      Emit_c.Ir_builder.finish state.builder (Goto test);
      Emit_c.Ir_builder.start state.builder after

let lower_for_each state ~(schedule : Lowering.schedule) ~(iteration : Mir.iteration)
    ~(each : Lowered.place -> unit) ~origin =
  let schedule =
    match schedule with
    | Chunked when not (Lowering.may_fork state) -> Lowering.Sequential
    | own -> own
  in
  let owned_each =
    match schedule with
    | Spawned loop -> fun value -> Mir_tasks.spawn_with_item state loop value ~owned:true ~each
    | Sequential | Chunked -> each
  in
  match iteration with
  | Range { start = low; stop = high; inclusive } ->
      lower_range_loop state ~schedule ~low ~high ~inclusive ~each
  | Pull { cursor; next } ->
      let cursor = Mir_places.lower_place state cursor in
      Targets.pull_loop state
        ~option:(Mir_calls.compute_result_type state next)
        ~call_next:(fun destination ->
          Mir_calls.lower_call_with_places state next [ cursor ] ~destination
            ~site:(Some (Mir_places.locate_site state origin)))
        ~body:owned_each
