let in_order = Fixtures.Concurrent.in_order

let expect_main ~expected text =
  let status, output, errors =
    Codegen_support.run_main (text ^ in_order ^ Fixtures.Concurrent.in_order_main)
  in
  if status <> 0 then Codegen_support.fail "ended with status %d: %s" status errors;
  Codegen_support.expect_string ~expected output

let passes_in_order name ~count source =
  Codegen_support.test name (fun () ->
      Codegen_support.expect_output (source ^ in_order)
        (String.concat "" (List.init count (Printf.sprintf "test %d passed\n"))))

let () =
  Codegen_support.test
    "branches use the enclosing capabilities and bind lets for the code after the block" (fun () ->
      expect_main ~expected:"first\nsecond\n20 22 made 3\n"
        Fixtures.Concurrent.concurrent_branches_building_a_pair);
  Codegen_support.test "a return in a branch returns its value, and later branches are not spawned"
    (fun () ->
      expect_main ~expected:"first ran\nsecond ran\nafter the block\n1\n7\n"
        Fixtures.Concurrent.leaves_returning_from_a_branch);
  Codegen_support.test "a ? in a branch returns the error and drops the lets of the other branches"
    (fun () ->
      expect_main ~expected:"sum 5\nfailed at second\nfailed at first\n"
        Fixtures.Concurrent.question_mark_in_a_concurrent_branch);
  Codegen_support.test "a task returns a result that is passed through a pointer" (fun () ->
      expect_main ~expected:"early 4 late 5\n" Fixtures.Concurrent.big_result_from_a_task);
  Codegen_support.test "break and continue in a branch apply to the loop that encloses the block"
    (fun () ->
      expect_main ~expected:"round 0\nbeside round 0\nround 2\nbeside round 2\n2\n"
        Fixtures.Concurrent.rounds_with_break_and_continue_in_branches)

let () =
  Codegen_support.test
    "continue ends one iteration, break cancels the loop, and return returns a value" (fun () ->
      expect_main
        ~expected:
          "iteration 0\n\
           iteration 1\n\
           iteration 3\n\
           before the break 0\n\
           after the loop\n\
           looked at 0\n\
           looked at 1\n\
           20\n\
           looked at 0\n\
           looked at 1\n\
           looked at 2\n\
           -1\n"
        Fixtures.Concurrent.concurrent_for_skipping_and_breaking);
  Codegen_support.test "a return ends every enclosing task and carries its value through each"
    (fun () ->
      expect_main
        ~expected:
          "checked item 0\n\
           beside item 0\n\
           done item 0\n\
           found item 1\n\
           checked item 0\n\
           beside item 0\n\
           done item 0\n\
           checked item 1\n\
           beside item 1\n\
           done item 1\n\
           none\n"
        Fixtures.Concurrent.nested_concurrent_for_returning_a_string);
  Codegen_support.test "break and continue in a branch apply to the enclosing concurrent for"
    (fun () ->
      expect_main ~expected:"first 0\nbeside 0\nafter block 0\nafter the loop\n"
        Fixtures.Concurrent.search_with_break_and_continue_in_branches);
  Codegen_support.test
    "a concurrent for over a range of characters and over a range of negative Int8 values"
    (fun () ->
      expect_main ~expected:"letter a\nletter b\nletter c\nsmall -2\nsmall -1\nsmall 0\n"
        Fixtures.Concurrent.concurrent_for_over_character_and_int8_ranges);
  Codegen_support.test "tasks call a capability implementation that is provided outside the loop"
    (fun () ->
      expect_main ~expected:"total 10\n" Fixtures.Concurrent.tally_provided_outside_the_loop);
  Codegen_support.test "tasks spawned inside a provide block capture its evidence" (fun () ->
      expect_main ~expected:"total 10 then 110\n"
        Fixtures.Concurrent.tally_provided_around_the_tasks);
  Codegen_support.test "a concurrent for over mut elements gives each task its own element"
    (fun () ->
      expect_main ~expected:"2 4 6\n2 4 3 at 3\n"
        Fixtures.Concurrent.concurrent_for_doubling_mut_elements);
  Codegen_support.test
    "a concurrent for over a stored cursor and over a temporary cursor of owned values" (fun () ->
      expect_main
        ~expected:
          "stored left 3\nstored left 2\nstored left 1\ntemporary left 4\ntemporary left 3\n2\n"
        Fixtures.Concurrent.concurrent_for_over_countdown_cursors);
  Codegen_support.test "a task gets a copy of a trivial value that a collection lends read-only"
    (fun () ->
      expect_main ~expected:"saw 5\nsaw 6\nsaw 7\n"
        Fixtures.Concurrent.bag_of_integers_lent_to_tasks)

let () =
  passes_in_order "a task borrows an element that a collection lends from a read-only parameter"
    ~count:3 Fixtures.Concurrent.bag_of_strings_lent_to_tasks;
  passes_in_order "a task owns a value that a cursor computes, and copies a plain one" ~count:2
    Fixtures.Concurrent.labels_cursor_owned_by_tasks

let () =
  passes_in_order "a task owns its item, and an item whose task is not spawned is dropped" ~count:2
    Fixtures.Concurrent.longest_owned_word;
  passes_in_order "a value returned through two nested tasks is neither leaked nor dropped twice"
    ~count:1 Fixtures.Concurrent.nested_concurrent_for_returning_a_list

let () =
  Codegen_support.passes "a return value that loses the cancel is dropped"
    Fixtures.Concurrent.spawns_when_cancelled

let expect_threaded ~expected text =
  let status, output, errors = Codegen_support.run_main text in
  if status <> 0 then Codegen_support.fail "ended with status %d: %s" status errors;
  Codegen_support.expect_string ~expected output

let () =
  Codegen_support.test
    "on threads, calls of a mut implementation by many tasks are mutually exclusive" (fun () ->
      expect_threaded ~expected:"total 40000 after 40000 calls\n"
        Fixtures.Concurrent.tally_called_by_many_tasks);
  Codegen_support.test
    "on threads, a task that waits on a key runs again when another task wakes the key" (fun () ->
      expect_threaded ~expected:"saw the flag\n" Fixtures.Concurrent.flag_waited_on_and_raised);
  Codegen_support.test "on threads, a return cancels a blocked task and the tasks it has spawned"
    (fun () ->
      expect_threaded ~expected:"5 cancelled true and nested true\n"
        Fixtures.Concurrent.return_cancelling_nested_tasks);
  Codegen_support.test "on threads, tasks take ownership of their items and free the blocks"
    (fun () -> expect_threaded ~expected:"total 1400\n" Fixtures.Concurrent.lengths_of_owned_items)

let expect_with_each_thread_count ~expected text =
  Fun.protect
    ~finally:(fun () -> Unix.putenv "TRUSS_WORKERS" "")
    (fun () ->
      List.iter
        (fun workers ->
          Unix.putenv "TRUSS_WORKERS" (string_of_int workers);
          expect_threaded ~expected text)
        Codegen_support.worker_counts)

let tally = Fixtures.Concurrent.tally

let () =
  Codegen_support.test
    "on threads, nested groups of tasks park, yield, block, and lock with any number of threads"
    (fun () ->
      expect_with_each_thread_count ~expected:"total 2000\n"
        (tally ^ Fixtures.Concurrent.nested_task_groups));
  Codegen_support.test
    "on threads, each run of a concurrent for and of a parallel for has its own drop flags"
    (fun () ->
      expect_threaded ~expected:"total 3000\nparallel total 2000\n"
        (tally ^ Fixtures.Concurrent.loops_with_drop_flags_run_repeatedly));
  Codegen_support.test "on threads, tasks run parallel blocks and loops with any number of threads"
    (fun () ->
      expect_with_each_thread_count ~expected:"total 40064\n"
        (tally ^ Fixtures.Concurrent.parallel_fib));
  Codegen_support.test
    "on threads, a task that leaves its thread in a coroutine resumes with any number of threads"
    (fun () ->
      expect_with_each_thread_count ~expected:"total 1920\n"
        Fixtures.Concurrent.coroutine_counter_on_many_threads)

let () =
  Codegen_support.test "on threads, more tasks sleep at once than the runtime has threads"
    (fun () ->
      expect_threaded ~expected:"600 woke first, before a sleep ended true\n"
        Fixtures.Concurrent.first_to_wake);
  Codegen_support.test
    "on threads, tasks connect, accept, read, and write on sockets with any number of threads"
    (fun () ->
      expect_with_each_thread_count ~expected:"echoed 16\n"
        ({|use standard::network

|} ^ tally ^ Fixtures.Concurrent.socket_echo_tasks));
  Codegen_support.test "on threads, a read in a task ends at the socket's time limit" (fun () ->
      expect_threaded ~expected:"timed out true\nthe peer closed true\n"
        Fixtures.Concurrent.socket_read_with_a_time_limit)

let child_lines = Fixtures.Concurrent.child_lines

let () =
  Codegen_support.test
    "on threads, tasks read and write the pipes of child processes with any number of threads"
    (fun () ->
      expect_with_each_thread_count
        ~expected:"captured 110890 and 110890\ncaptured from many\nechoed 262144\n"
        (child_lines ^ Fixtures.Concurrent.child_pipe_echo_tasks));
  Codegen_support.test "on one worker, both of a child's outputs are captured whole" (fun () ->
      Fun.protect
        ~finally:(fun () -> Unix.putenv "TRUSS_WORKERS" "")
        (fun () ->
          Unix.putenv "TRUSS_WORKERS" "1";
          expect_threaded ~expected:"captured 110890 and 110890\n"
            (child_lines ^ Fixtures.Concurrent.child_outputs_captured)))

let () =
  Codegen_support.test
    "on threads, a cancelled task returns from a call that blocks in the operating system"
    (fun () ->
      expect_threaded ~expected:"run: cancelled\ntimed out\n"
        Fixtures.Concurrent.discarded_sleep_with_a_time_out);
  Codegen_support.test "on threads, a cancelled task returns early from a sleep" (fun () ->
      expect_threaded ~expected:"1 early true\n" Fixtures.Concurrent.nap_with_a_cancelled_branch);
  Codegen_support.test "on threads, an accept in a cancelled task returns the cancelled error"
    (fun () ->
      expect_threaded ~expected:"accept: cancelled\ntimed out\n"
        Fixtures.Concurrent.accept_with_a_time_out);
  Codegen_support.test "on threads, a wait for signals in a cancelled task returns None" (fun () ->
      expect_threaded ~expected:"no signal\ntimed out\n"
        Fixtures.Concurrent.signal_wait_with_a_time_out);
  Codegen_support.test "on threads, a cancelled task returns from a wait for a child's output"
    (fun () ->
      expect_threaded ~expected:"run: cancelled\ntimed out\n"
        Fixtures.Concurrent.captured_sleep_with_a_time_out)
