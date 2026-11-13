(* [concurrent] blocks and loops. Whole programs use the runtime's [Tasks],
   which runs each task when it is spawned. Truss tests provide a [Tasks]
   written in Truss, and the test runner fails a test that leaks a heap
   block. *)

open Codegen_support

(* The output of a program whose tasks run sequentially, in the order they
   are spawned, so that the output shows which tasks ran. *)
let expect_main ~expected text =
  let status, output, errors = run_main ~in_order:true text in
  if status <> 0 then fail "ended with status %d: %s" status errors;
  expect_string ~expected output

(* A [Tasks] implementation in Truss that runs each task when it is
   spawned. *)
let in_order = Fixtures.Concurrent.in_order

(* A test of a module whose [count] tests all pass. [InOrder] is appended to
   the module. *)
let passes_in_order name ~count source =
  test name (fun () ->
      expect_output (source ^ in_order)
        (String.concat "" (List.init count (Printf.sprintf "test %d passed\n"))))

(* Blocks *)

let () =
  test "branches use the enclosing capabilities and bind lets for the code after the block"
    (fun () ->
      expect_main ~expected:"first\nsecond\n20 22 made 3\n"
        Fixtures.Concurrent.branches_use_the_enclosing_capabilities_and_bind);
  test "a return in a branch returns its value, and later branches are not spawned" (fun () ->
      expect_main ~expected:"first ran\nsecond ran\nafter the block\n1\n7\n"
        Fixtures.Concurrent.return_in_a_branch_returns_its_value_and_later);
  test "a ? in a branch returns the error and drops the lets of the other branches" (fun () ->
      expect_main ~expected:"sum 5\nfailed at second\nfailed at first\n"
        Fixtures.Concurrent.in_a_branch_returns_the_error_and_drops_the_lets);
  test "a task returns a result that is passed through a pointer" (fun () ->
      expect_main ~expected:"early 4 late 5\n"
        Fixtures.Concurrent.task_returns_a_result_that_is_passed_through_a);
  test "break and continue in a branch apply to the loop that encloses the block" (fun () ->
      expect_main ~expected:"round 0\nbeside round 0\nround 2\nbeside round 2\n2\n"
        Fixtures.Concurrent.break_and_continue_in_a_branch_apply_to_the_loop)

(* Loops *)

let () =
  test "continue ends one iteration, break cancels the loop, and return returns a value" (fun () ->
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
        Fixtures.Concurrent.continue_ends_one_iteration_break_cancels_the_loop);
  test "a return ends every enclosing task and carries its value through each" (fun () ->
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
        Fixtures.Concurrent.return_ends_every_enclosing_task_and_carries_its);
  test "break and continue in a branch apply to the enclosing concurrent for" (fun () ->
      expect_main ~expected:"first 0\nbeside 0\nafter block 0\nafter the loop\n"
        Fixtures.Concurrent.break_and_continue_in_a_branch_apply_to_the);
  test "a concurrent for over a range of characters and over a range of negative Int8 values"
    (fun () ->
      expect_main ~expected:"letter a\nletter b\nletter c\nsmall -2\nsmall -1\nsmall 0\n"
        Fixtures.Concurrent.concurrent_for_over_a_range_of_characters_and_over);
  test "tasks call a capability implementation that is provided outside the loop" (fun () ->
      expect_main ~expected:"total 10\n"
        Fixtures.Concurrent.tasks_call_a_capability_implementation_that_is);
  test "tasks spawned inside a provide block capture its evidence" (fun () ->
      expect_main ~expected:"total 10 then 110\n"
        Fixtures.Concurrent.tasks_spawned_inside_a_provide_block_capture_its);
  test "a concurrent for over mut elements gives each task its own element" (fun () ->
      expect_main ~expected:"2 4 6\n2 4 3 at 3\n"
        Fixtures.Concurrent.concurrent_for_over_mut_elements_gives_each_task);
  test "a concurrent for over a cursor and over a method that yields owned values" (fun () ->
      expect_main
        ~expected:"pulled left 3\npulled left 2\npulled left 1\ninlined left 4\ninlined left 3\n2\n"
        Fixtures.Concurrent.concurrent_for_over_a_cursor_and_over_a_method);
  test "a task gets a copy of a trivial value that a method yields read-only" (fun () ->
      expect_main ~expected:"saw 5\nsaw 6\nsaw 7\n"
        Fixtures.Concurrent.task_gets_a_copy_of_a_trivial_value_that_a_method)

(* Ownership of items and return values *)

let () =
  passes_in_order "a task borrows an element that a method lends from a read-only parameter"
    ~count:3 Fixtures.Concurrent.task_borrows_an_element_that_a_method_lends_from_a;
  passes_in_order "a task owns a value that a method computes, and copies a plain one" ~count:2
    Fixtures.Concurrent.task_owns_a_value_that_a_method_computes_and

let () =
  passes_in_order "a task owns its item, and an item whose task is not spawned is dropped" ~count:2
    Fixtures.Concurrent.task_owns_its_item_and_an_item_whose_task_is_not;
  passes_in_order "a value returned through two nested tasks is neither leaked nor dropped twice"
    ~count:1 Fixtures.Concurrent.value_returned_through_two_nested_tasks_is_neither

let () =
  passes "a return value that loses the cancel is dropped"
    Fixtures.Concurrent.return_value_that_loses_the_cancel_is_dropped

(* Tasks on threads *)

let expect_threaded ~expected text =
  let status, output, errors = run_main text in
  if status <> 0 then fail "ended with status %d: %s" status errors;
  expect_string ~expected output

let () =
  test "on threads, calls of a mut implementation by many tasks are mutually exclusive" (fun () ->
      expect_threaded ~expected:"total 40000 after 40000 calls\n"
        Fixtures.Concurrent.on_threads_calls_of_a_mut_implementation_by_many);
  test "on threads, a task that waits on a key runs again when another task wakes the key"
    (fun () ->
      expect_threaded ~expected:"saw the flag\n"
        Fixtures.Concurrent.on_threads_a_task_that_waits_on_a_key_runs_again);
  test "on threads, a return cancels a blocked task and the tasks it has spawned" (fun () ->
      expect_threaded ~expected:"5 cancelled true and nested true\n"
        Fixtures.Concurrent.on_threads_a_return_cancels_a_blocked_task_and_the);
  test "on threads, tasks take ownership of their items and free the blocks" (fun () ->
      expect_threaded ~expected:"total 1400\n"
        Fixtures.Concurrent.on_threads_tasks_take_ownership_of_their_items_and)

(* The scheduler, with each number of threads *)

let expect_with_each_thread_count ~expected text =
  Fun.protect
    ~finally:(fun () -> Unix.putenv "TRUSS_WORKERS" "")
    (fun () ->
      List.iter
        (fun workers ->
          Unix.putenv "TRUSS_WORKERS" (string_of_int workers);
          expect_threaded ~expected text)
        worker_counts)

let tally = Fixtures.Concurrent.tally

let () =
  test "on threads, nested groups of tasks park, yield, block, and lock with any number of threads"
    (fun () ->
      expect_with_each_thread_count ~expected:"total 2000\n"
        (tally ^ Fixtures.Concurrent.on_threads_nested_groups_of_tasks_park_yield_block));
  (* A flag that the runs shared would let one run drop a value that
     another had moved, or leave one that it still owned. *)
  test "on threads, each run of a concurrent for and of a parallel for has its own drop flags"
    (fun () ->
      expect_threaded ~expected:"total 3000\nparallel total 2000\n"
        (tally ^ Fixtures.Concurrent.on_threads_each_run_of_a_concurrent_for_and_of_a));
  test "on threads, tasks run parallel blocks and loops with any number of threads" (fun () ->
      expect_with_each_thread_count ~expected:"total 40064\n"
        (tally ^ Fixtures.Concurrent.on_threads_tasks_run_parallel_blocks_and_loops));
  (* The seeded scheduler runs its tasks as coroutines. [add] yields to the
     program's scheduler in one, so the task resumes on another thread
     while it is in a coroutine, and the other tasks park in theirs for
     the mutex. The coroutine then suspends on that thread, when it yields
     to the seeded scheduler. *)
  test "on threads, a task that leaves its thread in a coroutine resumes with any number of threads"
    (fun () ->
      expect_with_each_thread_count ~expected:"total 1920\n"
        Fixtures.Concurrent.on_threads_a_task_that_leaves_its_thread_in_a)

(* Waiting for time and for a socket *)

let () =
  (* A sleeping task that held a thread would keep the last task from
     running until a sleep ended: the runtime has fewer threads than this
     program has sleeping tasks. *)
  test "on threads, more tasks sleep at once than the runtime has threads" (fun () ->
      expect_threaded ~expected:"600 woke first, before a sleep ended true\n"
        Fixtures.Concurrent.on_threads_more_tasks_sleep_at_once_than_the);
  test "on threads, tasks connect, accept, read, and write on sockets with any number of threads"
    (fun () ->
      expect_with_each_thread_count ~expected:"echoed 16\n"
        ({|use standard::network

|} ^ tally
       ^ Fixtures.Concurrent.on_threads_tasks_connect_accept_read_and_write_on));
  test "on threads, a read in a task ends at the socket's time limit" (fun () ->
      expect_threaded ~expected:"timed out true\nthe peer closed true\n"
        Fixtures.Concurrent.on_threads_a_read_in_a_task_ends_at_the_sockets)

(* A child's pipes. Each of the child's two outputs is larger than a pipe
   holds, so the child ends only if both are read as it writes them. *)

let child_lines = Fixtures.Concurrent.child_lines

let () =
  test "on threads, tasks read and write the pipes of child processes with any number of threads"
    (fun () ->
      expect_with_each_thread_count
        ~expected:"captured 110890 and 110890\ncaptured from many\nechoed 262144\n"
        (child_lines ^ Fixtures.Concurrent.on_threads_tasks_read_and_write_the_pipes_of_child));
  test "in a program with one thread, both of a child's outputs are captured whole" (fun () ->
      expect_main ~expected:"captured 110890 and 110890\n"
        (child_lines ^ Fixtures.Concurrent.in_a_program_with_one_thread_both_of_a_childs))

(* Cancelling a task that waits *)

let () =
  (* The child's output is discarded. A child that inherited the program's
     output would keep it open after the program ended, and the test would
     wait for the child to end. *)
  test "on threads, a cancelled task returns from a call that blocks in the operating system"
    (fun () ->
      expect_threaded ~expected:"run: cancelled\ntimed out\n"
        Fixtures.Concurrent.on_threads_a_cancelled_task_returns_from_a_call);
  test "on threads, a cancelled task returns early from a sleep" (fun () ->
      expect_threaded ~expected:"1 early true\n"
        Fixtures.Concurrent.on_threads_a_cancelled_task_returns_early_from_a);
  test "on threads, an accept in a cancelled task returns the cancelled error" (fun () ->
      expect_threaded ~expected:"accept: cancelled\ntimed out\n"
        Fixtures.Concurrent.on_threads_an_accept_in_a_cancelled_task_returns);
  test "on threads, a wait for signals in a cancelled task returns None" (fun () ->
      expect_threaded ~expected:"no signal\ntimed out\n"
        Fixtures.Concurrent.on_threads_a_wait_for_signals_in_a_cancelled_task);
  test "on threads, a cancelled task returns from a wait for a child's output" (fun () ->
      expect_threaded ~expected:"run: cancelled\ntimed out\n"
        Fixtures.Concurrent.on_threads_a_cancelled_task_returns_from_a_wait)

(* Programs that are reported as not built *)

let unsupported name ~message text =
  test name (fun () ->
      match run_main text with
      | exception Failure raised -> expect_string ~expected:message raised
      | _ -> fail "the program was built")

let () =
  unsupported "concurrent code in a pulled method"
    ~message:
      "example/main.truss:5:3: Stage0 cannot build this yet: `concurrent` code in a yielding \
       method that is pulled."
    Fixtures.Concurrent.concurrent_code_in_a_pulled_method
