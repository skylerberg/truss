let check packages =
  Database.For_testing.list_diagnostics
    [ Resolve; Interface; Infer; Usage ]
    (Support.make_database packages)

let expect_one_diagnostic = Support.expect_one_diagnostic ~check
let expect_fine text = Support.expect_no_diagnostics ~check [ ("app.main", text) ]

let list_diagnostics text =
  Support.run_check ~check (Support.setup [ ("app.main", text) ]) "app.main"

let apply_machine_fixes text =
  Diagnostic.apply_edits text
    (List.concat_map
       (fun (diagnostic : Diagnostic.t) ->
         match diagnostic.fixes with [ fix ] -> fix.edits | _ -> [])
       (Diagnostic.list_machine_applicable (list_diagnostics text)))

let () =
  Harness.test "an unused binding with a constant's name and type offers the constant's path first"
    (fun () ->
      let text = Fixtures.Usage.is_test_of_a_name_like_a_constant in
      expect_one_diagnostic text "usage.unused_variable"
        ~says:
          "`lucky` is never used. A bare name in a pattern binds a variable, which matches every \
           value. To match the constant, write `app.main.lucky`.";
      Support.expect_error ~list_diagnostics text ~code:(Usage Unused_variable) ~at:"lucky"
        ~occurrence:2 ~fixed:Fixtures.Usage.is_test_of_a_name_like_a_constant_fixed
        ~alternatives:[ Fixtures.Usage.is_test_of_a_name_like_a_constant_as_wildcard ]);
  Harness.test "an unused binding with a constant's name and another type is replaced with _"
    (fun () ->
      expect_one_diagnostic Fixtures.Usage.is_test_of_a_name_like_a_constant_of_another_type
        "usage.unused_variable" ~says:"`lucky` is never used. Replace it with `_`.");
  Harness.test "an unused let binding with a constant's name is replaced with _" (fun () ->
      expect_one_diagnostic Fixtures.Usage.let_named_like_a_constant "usage.unused_variable"
        ~says:"`lucky` is never used. Replace it with `_`.");
  Harness.test "the machine-applicable fixes of an arm with a constant's name write its path"
    (fun () ->
      let fixed = apply_machine_fixes Fixtures.Usage.arm_named_like_a_constant in
      Harness.expect_string ~expected:Fixtures.Usage.arm_named_like_a_constant_fixed fixed;
      match list_diagnostics fixed with
      | [] -> ()
      | left -> Harness.fail "after the fixes: %s" (String.concat "; " (Support.list_codes left)))

let () =
  Harness.test "a variable nothing reads is an error with a fix that renames it _" (fun () ->
      expect_one_diagnostic Fixtures.Usage.unused_let "usage.unused_variable"
        ~says:"`count` is never used. Replace it with `_`." ~fixed:Fixtures.Usage.unused_let_fixed);
  Harness.test "an unused var is replaced with _" (fun () ->
      expect_one_diagnostic Fixtures.Usage.unused_var "usage.unused_variable"
        ~fixed:Fixtures.Usage.unused_var_fixed);
  Harness.test "a parameter nothing reads is not an error" (fun () ->
      expect_fine "fn f(count: Int64) {}\n");
  Harness.test "an unused lambda parameter is replaced with _" (fun () ->
      expect_one_diagnostic Fixtures.Usage.unused_lambda_parameter "usage.unused_variable"
        ~fixed:Fixtures.Usage.unused_lambda_parameter_fixed);
  Harness.test "an unused loop variable is replaced with _" (fun () ->
      expect_one_diagnostic Fixtures.Usage.unused_loop_variable "usage.unused_variable"
        ~fixed:Fixtures.Usage.unused_loop_variable_fixed);
  Harness.test "an unused binding of is is replaced with _" (fun () ->
      expect_one_diagnostic Fixtures.Usage.unused_binding_of_is "usage.unused_variable"
        ~fixed:Fixtures.Usage.unused_binding_of_is_fixed);
  Harness.test "an unused quantified variable is replaced with _" (fun () ->
      expect_one_diagnostic Fixtures.Usage.unused_quantified_variable "usage.unused_variable"
        ~fixed:Fixtures.Usage.unused_quantified_variable_fixed);
  Harness.test "an unused field of a record pattern is fixed by name" (fun () ->
      expect_one_diagnostic Fixtures.Usage.record_pattern_with_unused_field "usage.unused_variable"
        ~says:"`second` is never used. Match its field with `second: _`."
        ~fixed:Fixtures.Usage.record_pattern_with_unused_field_fixed);
  Harness.test "an unused name in a tuple pattern is replaced with _" (fun () ->
      expect_one_diagnostic Fixtures.Usage.tuple_pattern_with_an_unused_name "usage.unused_variable"
        ~says:"`name` is never used. Replace it with `_`."
        ~fixed:Fixtures.Usage.tuple_pattern_with_an_unused_name_fixed);
  Harness.test "a binding of the only field of a variant is replaced with _" (fun () ->
      expect_one_diagnostic Fixtures.Usage.match_arm_with_unused_binding "usage.unused_variable"
        ~says:"`value` is never used. Replace it with `_`."
        ~fixed:Fixtures.Usage.match_arm_with_unused_binding_fixed);
  Harness.test "an unused field beside .. is deleted" (fun () ->
      expect_one_diagnostic Fixtures.Usage.unused_field_beside_rest "usage.unused_variable"
        ~says:"`second` is never used. Delete it, since `..` matches its field."
        ~fixed:Fixtures.Usage.unused_field_beside_rest_fixed);
  Harness.test "the only written field beside .. is deleted" (fun () ->
      expect_one_diagnostic Fixtures.Usage.unused_only_written_field_beside_rest
        "usage.unused_variable" ~fixed:Fixtures.Usage.unused_only_written_field_beside_rest_fixed);
  Harness.test "a field matched by position beside .. is deleted" (fun () ->
      expect_one_diagnostic Fixtures.Usage.unused_positional_field_beside_rest
        "usage.unused_variable" ~fixed:Fixtures.Usage.unused_positional_field_beside_rest_fixed);
  Harness.test "an unused binding of an or-pattern is removed from every alternative" (fun () ->
      expect_one_diagnostic Fixtures.Usage.unused_binding_of_an_or_pattern "usage.unused_variable"
        ~says:"`code` is never used. Remove it from every alternative of the pattern."
        ~fixed:Fixtures.Usage.unused_binding_of_an_or_pattern_fixed);
  Harness.test "a binding of an or-pattern that its arm reads is not an error" (fun () ->
      expect_fine Fixtures.Usage.or_pattern_binding_read_by_its_arm);
  Harness.test "code after a return is unreachable, with a fix that deletes it" (fun () ->
      expect_one_diagnostic Fixtures.Usage.statement_after_return "usage.unreachable_code"
        ~fixed:Fixtures.Usage.statement_after_return_fixed);
  Harness.test "code after a loop that is never left is unreachable" (fun () ->
      expect_one_diagnostic Fixtures.Usage.statement_after_endless_loop "usage.unreachable_code");
  Harness.test "code after a loop that breaks is reachable" (fun () ->
      expect_fine Fixtures.Usage.statement_after_loop_that_breaks);
  Harness.test "code after todo is not unreachable" (fun () ->
      expect_fine Fixtures.Usage.statement_after_todo);
  Harness.test "if false is not reported" (fun () ->
      expect_fine Fixtures.Usage.return_under_if_false);
  Harness.test "a branch after one that returns still runs" (fun () ->
      expect_fine Fixtures.Usage.concurrent_branches_that_both_return);
  Harness.test "code after a block whose branch never finishes is unreachable" (fun () ->
      expect_one_diagnostic Fixtures.Usage.statement_after_concurrent_branches_that_return
        "usage.unreachable_code");
  Harness.test "a float compared with itself by != is an error with a fix that calls is_nan"
    (fun () ->
      expect_one_diagnostic Fixtures.Usage.self_comparison_of_a_float "usage.self_comparison"
        ~says:
          "`value != value` compares a value with itself, so it is always false. `==` treats every \
           NaN as equal to itself, so a test for NaN calls `value.is_nan()`."
        ~fixed:Fixtures.Usage.self_comparison_of_a_float_fixed);
  Harness.test "a float compared with itself by == is fixed to a negated is_nan" (fun () ->
      expect_one_diagnostic Fixtures.Usage.self_equality_of_a_float "usage.self_comparison"
        ~fixed:Fixtures.Usage.self_equality_of_a_float_fixed);
  Harness.test "an integer compared with itself is always true, and has no fix" (fun () ->
      expect_one_diagnostic "fn f(count: Int64) -> Bool {\n  count <= count\n}\n"
        "usage.self_comparison"
        ~says:"`count <= count` compares a value with itself, so it is always true.");
  Harness.test "an element compared with itself through one index is an error" (fun () ->
      expect_one_diagnostic
        "fn f(items: List[Int64], index: UInt64) -> Bool\n\
        \  requires index < items.length()\n\
         {\n\
        \  items[index] < items[index]\n\
         }\n"
        "usage.self_comparison" ~says:"always false");
  Harness.test "a field compared with itself is an error" (fun () ->
      expect_one_diagnostic
        "type Point(x: Int64, y: Int64)\n\n\
         fn Point.is_level(self) -> Bool {\n\
        \  self.x == self.x\n\
         }\n"
        "usage.self_comparison" ~says:"`self.x == self.x`");
  Harness.test "a specification may compare a value with itself" (fun () ->
      expect_fine Fixtures.Usage.comparisons_in_specifications);
  Harness.test "comparisons of different places and of calls are not reported" (fun () ->
      expect_fine Fixtures.Usage.comparisons_of_different_places)

let () =
  Harness.test "a var that is assigned and never read is unused, with no fix" (fun () ->
      expect_one_diagnostic Fixtures.Usage.var_only_assigned "usage.unused_variable"
        ~says:"`other` is assigned but never read. Delete it and its assignments, or read it.");
  Harness.test "a compound assignment reads its var" (fun () ->
      expect_fine Fixtures.Usage.var_assigned_and_read);
  Harness.test "writing through a mut binding changes the place it is bound to" (fun () ->
      expect_fine Fixtures.Usage.mut_bindings_written_through)

let () =
  let expect_removed text fixed = expect_one_diagnostic ~fixed text "usage.unused_run_forever" in
  Harness.test "a RunForever that nothing uses is reported, and removing it joins the brace"
    (fun () ->
      expect_removed Fixtures.Usage.run_forever_that_nothing_uses
        "fn f(values: List[UInt64]) -> UInt64 {\n\
        \  var total: UInt64 = 0\n\
        \  for value in values {\n\
        \    total = value\n\
        \  }\n\
        \  total\n\
         }\n");
  Harness.test "removing a RunForever listed after another capability keeps that capability"
    (fun () ->
      expect_removed Fixtures.Usage.run_forever_listed_after_another_capability
        "fn f(values: List[UInt64]) -> UInt64\n  uses Panic\n{\n  values.length() + 1\n}\n");
  Harness.test "removing a RunForever listed before another capability keeps that capability"
    (fun () ->
      expect_removed Fixtures.Usage.run_forever_listed_before_another_capability
        "fn f(values: List[UInt64]) -> UInt64\n  uses Panic\n{\n  values.length() + 1\n}\n");
  Harness.test "removing a RunForever before another clause keeps the brace on its own line"
    (fun () ->
      expect_removed Fixtures.Usage.run_forever_before_an_ensures
        "fn f(values: List[UInt64]) -> UInt64\n\
        \  ensures result == values.length()\n\
         {\n\
        \  values.length()\n\
         }\n");
  Harness.test "a RunForever is used by a recursion, which it leaves unchecked" (fun () ->
      expect_fine Fixtures.Usage.run_forever_of_a_recursion);
  Harness.test "a RunForever is used by a lambda passed to a generic callee that may run forever"
    (fun () -> expect_fine Fixtures.Usage.run_forever_of_a_lambda_passed_to_a_generic_callee);
  Harness.test "a RunForever is used by a call of a function that may run forever" (fun () ->
      expect_fine Fixtures.Usage.run_forever_of_a_callee_that_runs_forever);
  Harness.test "a RunForever is used by a while loop whose measure is its condition" (fun () ->
      expect_fine Fixtures.Usage.run_forever_of_a_while_loop_measured_by_its_condition);
  Harness.test "a RunForever is used by a while loop whose written measure has a condition"
    (fun () ->
      expect_fine Fixtures.Usage.run_forever_of_a_while_loop_whose_written_measure_has_a_condition);
  Harness.test "a while loop in a lambda does not use its enclosing function's RunForever"
    (fun () ->
      expect_one_diagnostic Fixtures.Usage.run_forever_beside_a_while_loop_in_a_lambda
        "usage.unused_run_forever")
