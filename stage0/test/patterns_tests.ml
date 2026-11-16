let check packages =
  Database.For_testing.list_diagnostics
    [ Resolve; Interface; Infer; Patterns ]
    (Support.database packages)

let one_diagnostic = Support.one_diagnostic ~check
let fine text = Support.no_diagnostics ~check [ ("app::main", text) ]
let priority = Fixtures.Patterns.priority

let message text =
  let packages = Support.setup [ ("app::main", text) ] in
  match check packages (Support.file_of "app::main") with
  | [ diagnostic ] -> diagnostic.message
  | actual -> failwith (Printf.sprintf "%d diagnostics" (List.length actual))

let () =
  Harness.test "a missing case is named" (fun () ->
      let text = priority ^ Fixtures.Patterns.option_match_missing_urgent in
      let actual = message text in
      let expected = "`Some(Urgent(_))` is not covered" in
      if not (String.includes ~affix:expected actual) then Harness.fail "message %S" actual);
  Harness.test "a missing case's fix adds an arm with todo" (fun () ->
      one_diagnostic Fixtures.Patterns.bool_match_missing_false "patterns.not_covered"
        ~fixed:Fixtures.Patterns.bool_match_missing_false_fixed);
  Harness.test "an arm earlier arms cover is an error with a fix that deletes it" (fun () ->
      one_diagnostic Fixtures.Patterns.wildcard_arm_after_every_case "patterns.unreachable_arm"
        ~fixed:Fixtures.Patterns.wildcard_arm_after_every_case_fixed);
  Harness.test "an alternative the alternatives before it cover is an error" (fun () ->
      one_diagnostic Fixtures.Patterns.repeated_none_alternative "patterns.unreachable_alternative");
  Harness.test "an arm with a guard does not cover its pattern" (fun () ->
      one_diagnostic Fixtures.Patterns.match_with_only_a_guarded_arm "patterns.not_covered");
  Harness.test "integer ranges that cover the type are exhaustive" (fun () ->
      fine Fixtures.Patterns.byte_ranges_covering_the_type);
  Harness.test "integer ranges that leave a gap name it" (fun () ->
      let actual = message Fixtures.Patterns.byte_ranges_with_a_gap in
      if not (String.includes ~affix:"`100`" actual) then Harness.fail "message %S" actual);
  Harness.test "a match on a string needs a pattern that matches everything" (fun () ->
      one_diagnostic Fixtures.Patterns.string_match_without_a_wildcard "patterns.not_covered");
  Harness.test "a match over several values is checked as one" (fun () ->
      fine Fixtures.Patterns.match_on_two_values_covering_every_pair);
  Harness.test "a match over several values misses a combination" (fun () ->
      one_diagnostic Fixtures.Patterns.match_on_two_values_missing_a_pair "patterns.not_covered");
  Harness.test "a pattern that can fail cannot be a let's" (fun () ->
      one_diagnostic Fixtures.Patterns.let_with_a_refutable_pattern "patterns.refutable");
  Harness.test "a record pattern cannot fail" (fun () ->
      fine Fixtures.Patterns.let_with_a_record_pattern);
  Harness.test "a constant in a pattern is its value" (fun () ->
      fine Fixtures.Patterns.constant_arm)

let () =
  let codes_of text =
    let packages = Support.setup [ ("app::main", text) ] in
    (match Support.parse_errors packages (Support.file_of "app::main") with
    | [] -> ()
    | errors -> Harness.fail "the test input does not parse: %s" (String.concat " " errors));
    Support.codes (check packages (Support.file_of "app::main"))
  in
  let expect text expected =
    match codes_of text with
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
  let codes_of text =
    Support.codes (check (Support.setup [ ("app::main", text) ]) (Support.file_of "app::main"))
  in
  Harness.test "a record constant covers the record it is" (fun () ->
      one_diagnostic Fixtures.Patterns.record_constant_and_record_arms "patterns.unreachable_arm");
  Harness.test "a match on a type that failed to parse reports nothing more" (fun () ->
      match codes_of Fixtures.Patterns.match_on_a_broken_type with
      | actual when List.mem "patterns.not_covered" actual ->
          Harness.fail "found [%s]" (String.concat "; " actual)
      | _ -> ());
  Harness.test "code that builds a type that failed to parse reports nothing more" (fun () ->
      List.iter
        (fun argument ->
          match
            codes_of
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
      match codes_of Fixtures.Patterns.arm_with_a_misspelled_variant with
      | actual when List.exists (fun code -> String.starts_with ~prefix:"patterns." code) actual ->
          Harness.fail "found [%s]" (String.concat "; " actual)
      | _ -> ())

let () =
  Harness.test "an alternative that an earlier arm covers is unreachable, even the first" (fun () ->
      one_diagnostic Fixtures.Patterns.alternative_an_earlier_arm_covers
        "patterns.unreachable_alternative"
        ~fixed:Fixtures.Patterns.alternative_an_earlier_arm_covers_fixed);
  Harness.test "a nested alternative that the one before covers is unreachable" (fun () ->
      one_diagnostic Fixtures.Patterns.repeated_nested_alternative
        "patterns.unreachable_alternative")

let () =
  Harness.test "character literals and ranges cover their values" (fun () ->
      one_diagnostic Fixtures.Patterns.character_range_and_literal_arms "patterns.unreachable_arm")
