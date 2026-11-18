let run_with_workers ~workers text =
  Unix.putenv "TRUSS_WORKERS" (string_of_int workers);
  let status, output, errors = Codegen_support.run_main text in
  if status <> 0 then Codegen_support.fail "ended with status %d: %s" status errors;
  output

let expect_same_with_any_workers text ~expected =
  List.iter
    (fun workers -> Codegen_support.expect_string ~expected (run_with_workers ~workers text))
    (Codegen_support.list_worker_counts ())

let () =
  Codegen_support.test
    "branches give results through lets, mutate their own parts, and call a lambda" (fun () ->
      expect_same_with_any_workers ~expected:"2500050000 2500000000 2 n100000 300000\n"
        Fixtures.Parallel.parallel_branches_with_totals);
  Codegen_support.test "a branch forks again at every depth of a recursion" (fun () ->
      expect_same_with_any_workers ~expected:"832040\n" Fixtures.Parallel.parallel_fib);
  Codegen_support.test
    "one branch moves a field out and another changes a second field, and the first is \
     reinitialized after" (fun () ->
      expect_same_with_any_workers ~expected:"first taken second!\n"
        Fixtures.Parallel.parallel_branches_moving_and_changing_a_pair)

let board = Fixtures.Parallel.board

let () =
  Codegen_support.test "a parallel for over a list mutates each element once" (fun () ->
      expect_same_with_any_workers ~expected:"7905322 same\n"
        (board ^ Fixtures.Parallel.parallel_for_mutating_a_list));
  Codegen_support.test "a region reads a parameter that the function is passed by pointer"
    (fun () ->
      expect_same_with_any_workers ~expected:"2 4 6 8\n"
        Fixtures.Parallel.doubled_through_a_pointer_parameter);
  Codegen_support.test "a parallel for over a list leaves each element at its position" (fun () ->
      expect_same_with_any_workers ~expected:"5050\n"
        Fixtures.Parallel.parallel_for_over_a_list_by_position);
  Codegen_support.test "a panic in an iteration of a parallel for over a range ends the program"
    (fun () ->
      Unix.putenv "TRUSS_WORKERS" "8";
      let status, _, errors =
        Codegen_support.run_main Fixtures.Parallel.parallel_for_with_a_panic
      in
      Codegen_support.expect_int ~expected:101 status;
      if not (String.includes ~affix:"the last one ran" errors) then
        Codegen_support.fail "reported %s" errors);
  Codegen_support.test "an empty range and a range of one run their bodies no times and once"
    (fun () ->
      Unix.putenv "TRUSS_WORKERS" "8";
      let status, _, errors =
        Codegen_support.run_main Fixtures.Parallel.parallel_for_over_empty_and_single_ranges
      in
      Codegen_support.expect_int ~expected:101 status;
      if not (String.includes ~affix:"minus three ran" errors) then
        Codegen_support.fail "reported %s" errors)

let () =
  Codegen_support.test "a parallel for over a range of characters steps over the surrogates"
    (fun () ->
      Unix.putenv "TRUSS_WORKERS" "8";
      let status, _, errors =
        Codegen_support.run_main
          Fixtures.Parallel.parallel_for_over_characters_around_the_surrogates
      in
      Codegen_support.expect_int ~expected:101 status;
      if not (String.includes ~affix:"the last character ran" errors) then
        Codegen_support.fail "reported %s" errors)

let () =
  Codegen_support.expect_pass
    "a test runs the branches of a parallel block and of a parallel for, in order"
    (board ^ Fixtures.Parallel.parallel_board_test)

let () =
  Codegen_support.test
    "an outlined function's own local goes with it, and a shared one is reached through its \
     environment" (fun () ->
      let int = Lowered.Value Codegen_support.int32 in
      let add left right =
        Lowered.Binary (Add, Codegen_support.copy left, Codegen_support.copy right)
      in
      let env = Codegen_support.make_shape_env () in
      let builder = Emit_c.Ir_builder.create env ~item:(Codegen_support.code_item "entry") in
      let parameter = Emit_c.Ir_builder.allocate_local builder int in
      let sum = Emit_c.Ir_builder.allocate_local builder int in
      let other = Emit_c.Ir_builder.allocate_local builder int in
      Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder);
      Emit_c.Ir_builder.emit builder
        (Assign (Codegen_support.at parameter, Use (Codegen_support.constant_int32 5)));
      let first =
        Emit_c.Ir_builder.outline builder ~index:0 ~parts:[] (fun () ->
            let own = Emit_c.Ir_builder.allocate_local builder ~name:"own" int in
            Emit_c.Ir_builder.emit builder
              (Assign (Codegen_support.at own, add parameter parameter));
            Emit_c.Ir_builder.emit builder (Assign (Codegen_support.at sum, add own parameter));
            Emit_c.Ir_builder.finish builder (Return None))
      in
      let second =
        Emit_c.Ir_builder.outline builder ~index:1 ~parts:[] (fun () ->
            Emit_c.Ir_builder.emit builder
              (Assign (Codegen_support.at other, Use (Codegen_support.copy parameter)));
            Emit_c.Ir_builder.finish builder (Return None))
      in
      let take_address holder =
        Lowered.Address { place = Codegen_support.at holder; writable = false }
      in
      Emit_c.Ir_builder.emit builder
        (Fork { branches = [ (0, take_address first); (1, take_address second) ] });
      Emit_c.Ir_builder.emit builder (Assign (Codegen_support.at sum, add sum other));
      Emit_c.Ir_builder.finish builder (Return (Some (Codegen_support.copy sum)));
      let fragment =
        Emit_c.Ir_builder.build builder { parameters = []; result = Some int; returns = true }
      in
      let c = Emit_c.For_testing.render_c fragment in
      List.iter
        (fun text ->
          if not (String.includes ~affix:text c) then Codegen_support.fail "no %s in:\n%s" text c)
        [ "f_capture0"; "f_capture1"; "int32_t l6_own;" ];
      if String.includes ~affix:"f_capture2" c then
        Codegen_support.fail "a function reaches three locals:\n%s" c;
      Codegen_support.expect_status 20 [ Codegen_support.make_program_fragment fragment ])

let () =
  Codegen_support.test
    "a coroutine runs when resumed, switches back when it suspends, and ends when it returns"
    (fun () ->
      let work : Ground.function_type =
        {
          parameters = [ (Read, Codegen_support.named "UInt64") ];
          result = Codegen_support.named "Unit";
          uses = [];
        }
      in
      let environment =
        [
          ( "count",
            Lowered.Pointer
              { target = Codegen_support.value Codegen_support.int32; writable = true } );
        ]
      in
      let count = Codegen_support.at ~projections:[ Deref; Field "count"; Deref ] 2 in
      let add amount = Lowered.Assign (count, Binary (Add, Copy count, amount)) in
      let coroutine =
        Codegen_support.function_ ~parameters:[ 0; 1; 4 ] ~environment
          [
            Codegen_support.local ~name:"environment" (Raw (Nullable_pointer Opaque));
            Codegen_support.local ~name:"item"
              (Codegen_support.value (Codegen_support.named "UInt64"));
            Codegen_support.local (Pointer { target = Environment 0; writable = false });
            Codegen_support.local (Codegen_support.value Codegen_support.int32);
            Codegen_support.local ~name:"capabilities" Convention.capabilities;
          ]
          [
            Codegen_support.block
              [
                Assign (Codegen_support.at 2, Use (Codegen_support.copy 0));
                Assign (Codegen_support.at 3, Convert (Codegen_support.copy 1, Integer Int32));
                add (Codegen_support.copy 3);
                Call { target = Intrinsic Coroutine_suspend; arguments = []; result = Discarded };
                add (Codegen_support.constant_int32 10);
              ]
              (Return None);
          ]
      in
      let resume into : Lowered.statement =
        Call
          {
            target = Intrinsic Coroutine_resume;
            arguments = [ Codegen_support.copy 3 ];
            result = Returned (Codegen_support.at into);
          }
      in
      let add_amount amount =
        Lowered.Assign (Codegen_support.at 6, Binary (Add, Codegen_support.copy 6, amount))
      in
      Codegen_support.expect_status 112
        [
          Codegen_support.entry ~nested:[ coroutine ]
            [
              Codegen_support.local ~name:"count" (Codegen_support.value Codegen_support.int32);
              Codegen_support.local (Environment 0);
              Codegen_support.local (Codegen_support.value (Function work));
              Codegen_support.local (Codegen_support.value Codegen_support.uint64);
              Codegen_support.local (Raw Bool);
              Codegen_support.local (Raw Bool);
              Codegen_support.local (Codegen_support.value Codegen_support.int32);
              Codegen_support.local (Codegen_support.value Codegen_support.int32);
              Codegen_support.local (Codegen_support.value Codegen_support.int32);
            ]
            [
              Codegen_support.block
                [
                  Assign (Codegen_support.at 0, Use (Codegen_support.constant_int32 0));
                  Assign
                    ( Codegen_support.at ~projections:[ Field "count" ] 1,
                      Use (Address { place = Codegen_support.at 0; writable = true }) );
                  Assign
                    ( Codegen_support.at 2,
                      Function_value
                        {
                          code = Nested 0;
                          environment =
                            Some (Address { place = Codegen_support.at 1; writable = false });
                        } );
                  Call
                    {
                      target = Intrinsic Coroutine_start;
                      arguments = [ Codegen_support.copy 2; Constant (Integer (UInt64, Z.one)) ];
                      result = Returned (Codegen_support.at 3);
                    };
                  resume 4;
                  Assign (Codegen_support.at 6, Use (Codegen_support.copy 0));
                  resume 5;
                  Assign (Codegen_support.at 7, Convert (Codegen_support.copy 4, Integer Int32));
                  Assign (Codegen_support.at 8, Convert (Codegen_support.copy 5, Integer Int32));
                  Assign
                    ( Codegen_support.at 7,
                      Binary (Multiply, Codegen_support.copy 7, Codegen_support.constant_int32 100)
                    );
                  Assign
                    ( Codegen_support.at 8,
                      Binary (Multiply, Codegen_support.copy 8, Codegen_support.constant_int32 50)
                    );
                  add_amount (Codegen_support.copy 0);
                  add_amount (Codegen_support.copy 7);
                  add_amount (Codegen_support.copy 8);
                ]
                (Return (Some (Codegen_support.copy 6)));
            ];
        ])
