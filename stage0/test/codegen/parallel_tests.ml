(* [parallel] blocks and loops in whole programs, whose branches run on the
   runtime's threads, and in a test, where they run in order. *)

open Codegen_support

(* A program's output with a number of threads, which changes nothing a
   program does. More threads than cores makes them cross more often. *)
let output_with ~workers text =
  Unix.putenv "TRUSS_WORKERS" (string_of_int workers);
  let status, output, errors = run_main text in
  if status <> 0 then fail "ended with status %d: %s" status errors;
  output

let same_with_any_workers text ~expected =
  List.iter (fun workers -> expect_string ~expected (output_with ~workers text)) worker_counts

let () =
  test "branches give results through lets, change their own parts, and call a lambda" (fun () ->
      same_with_any_workers ~expected:"2500050000 2500000000 2 n100000 300000\n"
        Fixtures.Parallel.branches_give_results_through_lets_change_their);
  test "a branch forks again at every depth of a recursion" (fun () ->
      same_with_any_workers ~expected:"832040\n"
        Fixtures.Parallel.branch_forks_again_at_every_depth_of_a_recursion);
  test
    "one branch moves a field out and another changes a second field, and the first is \
     reinitialized after" (fun () ->
      same_with_any_workers ~expected:"first taken second!\n"
        Fixtures.Parallel.one_branch_moves_a_field_out_and_another_changes_a)

let board = Fixtures.Parallel.board

let () =
  test "a parallel for over a method that yields by position changes each element once" (fun () ->
      same_with_any_workers ~expected:"7905322 same\n"
        (board ^ Fixtures.Parallel.parallel_for_over_a_method_that_yields_by_position));
  test "a region reads a parameter that the function is passed by pointer" (fun () ->
      same_with_any_workers ~expected:"2 4 6 8\n"
        Fixtures.Parallel.region_reads_a_parameter_that_the_function_is);
  test "a parallel for over a list, whose each keeps a count between yields, runs in order"
    (fun () ->
      same_with_any_workers ~expected:"5050\n"
        Fixtures.Parallel.parallel_for_over_a_list_whose_each_keeps_a_count);
  test "a panic in an iteration of a parallel for over a range ends the program" (fun () ->
      Unix.putenv "TRUSS_WORKERS" "8";
      let status, _, errors =
        run_main Fixtures.Parallel.panic_in_an_iteration_of_a_parallel_for_over_a
      in
      expect_int ~expected:101 status;
      if not (contains errors "the last one ran") then fail "reported %s" errors);
  test "an empty range and a range of one run their bodies no times and once" (fun () ->
      Unix.putenv "TRUSS_WORKERS" "8";
      let status, _, errors =
        run_main Fixtures.Parallel.empty_range_and_a_range_of_one_run_their_bodies_no
      in
      expect_int ~expected:101 status;
      if not (contains errors "minus three ran") then fail "reported %s" errors)

let () =
  test "a parallel for over a range of characters steps over the surrogates" (fun () ->
      Unix.putenv "TRUSS_WORKERS" "8";
      let status, _, errors =
        run_main Fixtures.Parallel.parallel_for_over_a_range_of_characters_steps_over
      in
      expect_int ~expected:101 status;
      if not (contains errors "the last character ran") then fail "reported %s" errors)

let () =
  passes "a test runs the branches of a parallel block and of a parallel for, in order"
    (board ^ Fixtures.Parallel.test_runs_the_branches_of_a_parallel_block_and_of)

(* Outlining *)

let () =
  test
    "an outlined function's own local goes with it, and a shared one is reached through its \
     environment" (fun () ->
      let int = Lir.Value int32 in
      let add left right = Lir.Binary (Add, copy left, copy right) in
      let env = shape_env () in
      let builder = Emit_c.Builder.create env ~key:(key "entry") in
      let parameter = Emit_c.Builder.local builder int in
      let sum = Emit_c.Builder.local builder int in
      let other = Emit_c.Builder.local builder int in
      Emit_c.Builder.start builder (Emit_c.Builder.block builder);
      Emit_c.Builder.emit builder (Assign (at parameter, Use (constant_int32 5)));
      let first =
        Emit_c.Builder.outline builder ~nested:0 ~parts:[] (fun () ->
            let own = Emit_c.Builder.local builder ~name:"own" int in
            Emit_c.Builder.emit builder (Assign (at own, add parameter parameter));
            Emit_c.Builder.emit builder (Assign (at sum, add own parameter));
            Emit_c.Builder.finish builder (Return None))
      in
      let second =
        Emit_c.Builder.outline builder ~nested:1 ~parts:[] (fun () ->
            Emit_c.Builder.emit builder (Assign (at other, Use (copy parameter)));
            Emit_c.Builder.finish builder (Return None))
      in
      let address holder = Lir.Address { place = at holder; writable = false } in
      Emit_c.Builder.emit builder (Fork { branches = [ (0, address first); (1, address second) ] });
      Emit_c.Builder.emit builder (Assign (at sum, add sum other));
      Emit_c.Builder.finish builder (Return (Some (copy sum)));
      Emit_c.Builder.build builder ~parameters:[] ~result:(Some int);
      let instance = Emit_c.Builder.built builder in
      let c = Emit_c.For_testing.c (Emit_c.fragment env (Code instance)) in
      (* Each function reaches two locals of the entry, and the first keeps
         its own. *)
      List.iter
        (fun text -> if not (contains c text) then fail "no %s in:\n%s" text c)
        [ "f_capture0"; "f_capture1"; "l6_own = 0;" ];
      if contains c "f_capture2" then fail "a function reaches three locals:\n%s" c;
      expect_status 20 [ printed instance ])

(* Coroutines *)

let () =
  test "a coroutine runs when resumed, switches back when it suspends, and ends when it returns"
    (fun () ->
      (* The coroutine adds its item to a count, suspends, and adds 10. The
         entry reads the count after each resume, and the result of each
         resume. *)
      let work : Ground.function_type =
        { parameters = [ (Read, named "UInt64") ]; result = Returns (named "Unit"); uses = [] }
      in
      let environment = [ ("count", Lir.Pointer { target = value int32; writable = true }) ] in
      let count = at ~projections:[ Deref; Field "count"; Deref ] 2 in
      let add amount = Lir.Assign (count, Binary (Add, Copy count, amount)) in
      let coroutine =
        function_ ~parameters:[ 0; 1 ] ~environment
          [
            local ~name:"environment" (Raw (Nullable_pointer Opaque));
            local ~name:"item" (value (named "UInt64"));
            local (Pointer { target = Environment 0; writable = false });
            local (value int32);
          ]
          [
            block
              [
                Assign (at 2, Use (copy 0));
                Assign (at 3, Convert (copy 1, Integer Int32));
                add (copy 3);
                Call { target = Intrinsic Coroutine_suspend; arguments = []; result = Discarded };
                add (constant_int32 10);
              ]
              (Return None);
          ]
      in
      let resume into : Lir.statement =
        Call
          {
            target = Intrinsic Coroutine_resume;
            arguments = [ copy 3 ];
            result = Returned (at into);
          }
      in
      let plus amount = Lir.Assign (at 6, Binary (Add, copy 6, amount)) in
      expect_status 112
        [
          entry ~nested:[ coroutine ]
            [
              local ~name:"count" (value int32);
              local (Environment 0);
              local (value (Function work));
              local (value usize);
              local (Raw Bool);
              local (Raw Bool);
              local (value int32);
              local (value int32);
              local (value int32);
            ]
            [
              block
                [
                  Assign (at 0, Use (constant_int32 0));
                  Assign
                    ( at ~projections:[ Field "count" ] 1,
                      Use (Address { place = at 0; writable = true }) );
                  Assign
                    ( at 2,
                      Function_value
                        {
                          code = Nested 0;
                          environment = Some (Address { place = at 1; writable = false });
                        } );
                  Call
                    {
                      target = Intrinsic Coroutine_start;
                      arguments = [ copy 2; Constant (Integer (UInt64, Z.one)) ];
                      result = Returned (at 3);
                    };
                  resume 4;
                  Assign (at 6, Use (copy 0));
                  resume 5;
                  Assign (at 7, Convert (copy 4, Integer Int32));
                  Assign (at 8, Convert (copy 5, Integer Int32));
                  Assign (at 7, Binary (Multiply, copy 7, constant_int32 100));
                  Assign (at 8, Binary (Multiply, copy 8, constant_int32 50));
                  plus (copy 0);
                  plus (copy 7);
                  plus (copy 8);
                ]
                (Return (Some (copy 6)));
            ];
        ])
