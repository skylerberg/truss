open Harness
open Support

let check packages =
  Database.For_testing.(list_diagnostics [ Resolve; Interface; Infer; Patterns; Usage ])
    (Support.database packages)

let one_diagnostic = one_diagnostic ~check
let fine text = no_diagnostics ~check [ ("app::main", text) ]

let () =
  test "a variable nothing reads is an error with a fix that renames it _" (fun () ->
      one_diagnostic Fixtures.Usage.variable_nothing_reads_is_an_error_with_a_fix_that
        "usage.unused_variable" ~says:"`count` is never used. Replace it with `_`."
        ~fixed:Fixtures.Usage.variable_nothing_reads_is_an_error_with_a_fix_that_fixed);
  test "an unused var is replaced with _" (fun () ->
      one_diagnostic Fixtures.Usage.unused_var "usage.unused_variable"
        ~fixed:Fixtures.Usage.unused_var_fixed);
  test "a parameter nothing reads is not an error" (fun () -> fine "fn f(count: Int64) {}\n");
  test "an unused lambda parameter is replaced with _" (fun () ->
      one_diagnostic Fixtures.Usage.unused_lambda_parameter "usage.unused_variable"
        ~fixed:Fixtures.Usage.unused_lambda_parameter_fixed);
  test "an unused loop variable is replaced with _" (fun () ->
      one_diagnostic Fixtures.Usage.unused_loop_variable "usage.unused_variable"
        ~fixed:Fixtures.Usage.unused_loop_variable_fixed);
  test "an unused binding of is is replaced with _" (fun () ->
      one_diagnostic Fixtures.Usage.unused_binding_of_is "usage.unused_variable"
        ~fixed:Fixtures.Usage.unused_binding_of_is_fixed);
  test "an unused quantified variable is replaced with _" (fun () ->
      one_diagnostic Fixtures.Usage.unused_quantified_variable "usage.unused_variable"
        ~fixed:Fixtures.Usage.unused_quantified_variable_fixed);
  test "an unused field of a record pattern is fixed by name" (fun () ->
      one_diagnostic Fixtures.Usage.unused_field_of_a_record_pattern_is_fixed_by_name
        "usage.unused_variable" ~says:"`second` is never used. Match its field with `second: _`."
        ~fixed:Fixtures.Usage.unused_field_of_a_record_pattern_is_fixed_by_name_fixed);
  test "a binding of the only field of a variant is replaced with _" (fun () ->
      one_diagnostic Fixtures.Usage.binding_in_a_match_arm_must_be_used "usage.unused_variable"
        ~says:"`value` is never used. Replace it with `_`."
        ~fixed:Fixtures.Usage.binding_in_a_match_arm_must_be_used_fixed);
  test "an unused field beside .. is deleted" (fun () ->
      one_diagnostic Fixtures.Usage.unused_field_beside_rest "usage.unused_variable"
        ~says:"`second` is never used. Delete it, since `..` matches its field."
        ~fixed:Fixtures.Usage.unused_field_beside_rest_fixed);
  test "the only written field beside .. is deleted" (fun () ->
      one_diagnostic Fixtures.Usage.unused_only_written_field_beside_rest "usage.unused_variable"
        ~fixed:Fixtures.Usage.unused_only_written_field_beside_rest_fixed);
  test "a field matched by position beside .. is deleted" (fun () ->
      one_diagnostic Fixtures.Usage.unused_positional_field_beside_rest "usage.unused_variable"
        ~fixed:Fixtures.Usage.unused_positional_field_beside_rest_fixed);
  test "an unused binding of an or-pattern is removed from every alternative" (fun () ->
      one_diagnostic Fixtures.Usage.unused_binding_of_an_or_pattern "usage.unused_variable"
        ~says:"`code` is never used. Remove it from every alternative of the pattern."
        ~fixed:Fixtures.Usage.unused_binding_of_an_or_pattern_fixed);
  test "a binding of an or-pattern that its arm reads is not an error" (fun () ->
      fine Fixtures.Usage.or_pattern_binding_read_by_its_arm);
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
