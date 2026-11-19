let check packages =
  Database.For_testing.list_diagnostics
    [ Resolve; Interface; Infer; Patterns ]
    (Support.make_database packages)

let expect_one_diagnostic = Support.expect_one_diagnostic ~check
let expect_fine text = Support.expect_no_diagnostics ~check [ ("app::main", text) ]
let priority = Fixtures.Patterns.priority

let read_message text =
  let packages = Support.setup [ ("app::main", text) ] in
  match check packages (Support.parse_file "app::main") with
  | [ diagnostic ] -> diagnostic.message
  | actual -> failwith (Printf.sprintf "%d diagnostics" (List.length actual))

let () =
  Harness.test "a missing case is named" (fun () ->
      let text = priority ^ Fixtures.Patterns.option_match_missing_urgent in
      let actual = read_message text in
      let expected = "`Some(Urgent(_))` is not covered" in
      if not (String.includes ~affix:expected actual) then Harness.fail "message %S" actual);
  Harness.test "a missing case's fix adds an arm with todo" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.bool_match_missing_false "patterns.not_covered"
        ~fixed:Fixtures.Patterns.bool_match_missing_false_fixed);
  Harness.test "an arm earlier arms cover is an error with a fix that deletes it" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.wildcard_arm_after_every_case
        "patterns.unreachable_arm" ~fixed:Fixtures.Patterns.wildcard_arm_after_every_case_fixed);
  Harness.test "an alternative the alternatives before it cover is an error" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.repeated_none_alternative
        "patterns.unreachable_alternative");
  Harness.test "an arm with a guard does not cover its pattern" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.match_with_only_a_guarded_arm "patterns.not_covered");
  Harness.test "integer ranges that cover the type are exhaustive" (fun () ->
      expect_fine Fixtures.Patterns.byte_ranges_covering_the_type);
  Harness.test "integer ranges that leave a gap name it" (fun () ->
      let actual = read_message Fixtures.Patterns.byte_ranges_with_a_gap in
      if not (String.includes ~affix:"`100`" actual) then Harness.fail "message %S" actual);
  Harness.test "a match on a string needs a pattern that matches everything" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.string_match_without_a_wildcard "patterns.not_covered");
  Harness.test "a match over several values is checked as one" (fun () ->
      expect_fine Fixtures.Patterns.match_on_two_values_covering_every_pair);
  Harness.test "a match over several values misses a combination" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.match_on_two_values_missing_a_pair
        "patterns.not_covered");
  Harness.test "a pattern that can fail cannot be a let's" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.let_with_a_refutable_pattern "patterns.refutable");
  Harness.test "a record pattern cannot fail" (fun () ->
      expect_fine Fixtures.Patterns.let_with_a_record_pattern);
  Harness.test "a constant in a pattern is its value" (fun () ->
      expect_fine Fixtures.Patterns.constant_arm)

let () =
  let list_codes text =
    let packages = Support.setup [ ("app::main", text) ] in
    Support.list_codes (Support.run_check ~check packages "app::main")
  in
  let expect text expected =
    match list_codes text with
    | actual when actual = expected -> ()
    | actual -> Harness.fail "found [%s]" (String.concat "; " actual)
  in
  Harness.test "a qualified constant covers only its value" (fun () ->
      expect Fixtures.Patterns.qualified_constant_arm [ "patterns.not_covered" ]);
  Harness.test "a range with a constant end covers only up to it" (fun () ->
      expect Fixtures.Patterns.range_from_a_constant_and_literals
        [ "patterns.unreachable_alternative" ]);
  Harness.test "a range with a constant end is not a wildcard" (fun () ->
      expect Fixtures.Patterns.only_a_range_from_a_constant [ "patterns.not_covered" ]);
  Harness.test "a Bool constant covers its value" (fun () ->
      expect Fixtures.Patterns.bool_constant_and_false_arms []);
  Harness.test "a variant constant covers its variant" (fun () ->
      expect Fixtures.Patterns.variant_constant_arm []);
  Harness.test "a constant whose value is not evaluated at compile time covers only itself"
    (fun () -> expect Fixtures.Patterns.unevaluated_constant_arm []);
  Harness.test "a range with Character constant ends covers their values" (fun () ->
      expect Fixtures.Patterns.range_between_character_constants [ "patterns.unreachable_arm" ]);
  Harness.test "ranges that share an unevaluated end are distinct" (fun () ->
      expect Fixtures.Patterns.ranges_from_an_unevaluated_constant [])

let () =
  let list_codes text =
    Support.list_codes
      (check (Support.setup [ ("app::main", text) ]) (Support.parse_file "app::main"))
  in
  Harness.test "a record constant covers the record it is" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.record_constant_and_record_arms
        "patterns.unreachable_arm");
  Harness.test "a match on a type that failed to parse reports nothing more" (fun () ->
      match list_codes Fixtures.Patterns.match_on_a_broken_type with
      | actual when List.mem "patterns.not_covered" actual ->
          Harness.fail "found [%s]" (String.concat "; " actual)
      | _ -> ());
  Harness.test "code that builds a type that failed to parse reports nothing more" (fun () ->
      List.iter
        (fun argument ->
          match
            list_codes
              ("type Entry = {\n\
               \  name: String\n\
                }\n\n\
                fn built(name: String) -> Entry {\n\
               \  Entry(name: " ^ argument ^ ")\n}\n")
          with
          | [] -> ()
          | actual -> Harness.fail "found [%s]" (String.concat "; " actual))
        [ "own name"; "\"${name}\"" ]);
  Harness.test "a sub-pattern that failed to type makes no arm unreachable" (fun () ->
      match list_codes Fixtures.Patterns.arm_with_a_misspelled_variant with
      | actual when List.exists (fun code -> String.starts_with ~prefix:"patterns." code) actual ->
          Harness.fail "found [%s]" (String.concat "; " actual)
      | _ -> ())

let () =
  Harness.test "an alternative that an earlier arm covers is unreachable, even the first" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.alternative_an_earlier_arm_covers
        "patterns.unreachable_alternative"
        ~fixed:Fixtures.Patterns.alternative_an_earlier_arm_covers_fixed);
  Harness.test "a nested alternative that the one before covers is unreachable" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.repeated_nested_alternative
        "patterns.unreachable_alternative")

let () =
  Harness.test "character literals and ranges cover their values" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.character_range_and_literal_arms
        "patterns.unreachable_arm")
