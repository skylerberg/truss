(* The tests of the rules on use: unused variables and unreachable code. *)

open Harness
open Support

let check = Type_checker.For_testing.through Usage
let one_diagnostic = one_diagnostic ~check
let fine text = no_diagnostics ~check [ ("app::main", text) ]

let () =
  test "a variable nothing reads is an error with a fix that renames it _" (fun () ->
      one_diagnostic Fixtures.Usage.variable_nothing_reads_is_an_error_with_a_fix_that
        "usage.unused_variable"
        ~fixed:Fixtures.Usage.variable_nothing_reads_is_an_error_with_a_fix_that_fixed);
  test "a parameter nothing reads is not an error" (fun () ->
      fine "fn run_example(count: Int64) {}\n");
  test "an unused field of a record pattern is fixed by name" (fun () ->
      one_diagnostic Fixtures.Usage.unused_field_of_a_record_pattern_is_fixed_by_name
        "usage.unused_variable"
        ~fixed:Fixtures.Usage.unused_field_of_a_record_pattern_is_fixed_by_name_fixed);
  test "a binding in a match arm must be used" (fun () ->
      one_diagnostic Fixtures.Usage.binding_in_a_match_arm_must_be_used "usage.unused_variable");
  test "code after a return is unreachable, with a fix that deletes it" (fun () ->
      one_diagnostic Fixtures.Usage.code_after_a_return_is_unreachable_with_a_fix_that
        "usage.unreachable_code"
        ~fixed:Fixtures.Usage.code_after_a_return_is_unreachable_with_a_fix_that_fixed);
  test "code after a loop that is never left is unreachable" (fun () ->
      one_diagnostic Fixtures.Usage.code_after_a_loop_that_is_never_left_is "usage.unreachable_code");
  test "code after a loop that breaks is reachable" (fun () ->
      fine Fixtures.Usage.code_after_a_loop_that_breaks_is_reachable);
  test "code after todo is not unreachable" (fun () ->
      fine Fixtures.Usage.code_after_todo_is_not_unreachable);
  test "if false is not reported" (fun () -> fine Fixtures.Usage.if_false_is_not_reported);
  test "a branch after one that returns still runs" (fun () ->
      fine Fixtures.Usage.branch_after_one_that_returns_still_runs);
  test "code after a block whose branch never finishes is unreachable" (fun () ->
      one_diagnostic Fixtures.Usage.code_after_a_block_whose_branch_never_finishes_is
        "usage.unreachable_code")
