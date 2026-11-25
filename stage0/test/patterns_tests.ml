let check packages =
  Database.For_testing.list_diagnostics [ Resolve; Interface; Infer ]
    (Support.make_database packages)

let expect_one_diagnostic = Support.expect_one_diagnostic ~check
let expect_fine text = Support.expect_no_diagnostics ~check [ ("app.main", text) ]
let priority = Fixtures.Patterns.priority

let read_message text =
  let packages = Support.setup [ ("app.main", text) ] in
  match check packages (Support.parse_file "app.main") with
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
        ~fixed:("true => 1\n  }\n}", "true => 1\n    false => todo\n  }\n}"));
  Harness.test "an arm earlier arms cover is an error with a fix that deletes it" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.wildcard_arm_after_every_case
        "patterns.unreachable_arm" ~fixed:("  _ => 1\n  }", "}"));
  Harness.test "an alternative the alternatives before it cover is an error" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.repeated_none_alternative
        "patterns.unreachable_alternative" ~fixed:("None | None => 0", "None => 0"));
  Harness.test "an arm with a guard does not cover its pattern" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.match_with_only_a_guarded_arm "patterns.not_covered"
        ~fixed:("value if value > 0 => 1\n  }\n}", "value if value > 0 => 1\n    _ => todo\n  }\n}"));
  Harness.test "integer ranges that cover the type are exhaustive" (fun () ->
      expect_fine Fixtures.Patterns.byte_ranges_covering_the_type);
  Harness.test "a match that misses two cases names one and counts the other" (fun () ->
      let actual = read_message Fixtures.Patterns.match_missing_two_variants in
      let expected = "`Green` is not covered, nor 1 other." in
      if not (String.includes ~affix:expected actual) then Harness.fail "message %S" actual);
  Harness.test "integer ranges that leave a gap name it" (fun () ->
      let actual = read_message Fixtures.Patterns.byte_ranges_with_a_gap in
      if not (String.includes ~affix:"`100`" actual) then Harness.fail "message %S" actual);
  Harness.test "a match on a string needs a pattern that matches everything" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.string_match_without_a_wildcard "patterns.not_covered"
        ~fixed:("\"a\" => 1\n  }\n}", "\"a\" => 1\n    _ => todo\n  }\n}"));
  Harness.test "a match over several values is checked as one" (fun () ->
      expect_fine Fixtures.Patterns.match_on_two_values_covering_every_pair);
  Harness.test "a match over several values misses a combination" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.match_on_two_values_missing_a_pair
        "patterns.not_covered"
        ~fixed:("Running, _ => 2\n  }\n}", "Running, _ => 2\n    Idle, Stop => todo\n  }\n}"));
  Harness.test "a pattern that can fail cannot be a let's" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.let_with_a_refutable_pattern "patterns.refutable");
  Harness.test "a record pattern cannot fail" (fun () ->
      expect_fine Fixtures.Infer.let_binding_both_fields_of_a_pair);
  Harness.test "a constant in a pattern is its value" (fun () ->
      expect_fine Fixtures.Patterns.constant_arm);
  Harness.test "an arm that a binding with a constant's name covers is fixed by the constant's path"
    (fun () ->
      expect_one_diagnostic Fixtures.Patterns.arm_after_a_variant_binding_named_like_a_constant
        "patterns.unreachable_arm"
        ~says:
          "`lucky` in an earlier arm binds a variable, which matches every value. To match the \
           constant, write `app.main.lucky`."
        ~fixed:("Some(lucky) => 2", "Some(app.main.lucky) => 2"));
  Harness.test "an arm that the constant also covers is deleted" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.arm_that_the_constant_also_covers
        "patterns.unreachable_arm" ~fixed:("  7 => 2\n  }", "}"));
  Harness.test "a field bound by its own name is not read as a constant" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.arm_after_a_field_bound_by_its_name
        "patterns.unreachable_arm" ~fixed:("  (..) => 2\n  }", "}"))

let () =
  let list_codes text =
    let packages = Support.setup [ ("app.main", text) ] in
    Support.list_codes (Support.run_check ~check packages "app.main")
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
  Harness.test "a constant in a contract's pattern covers its value" (fun () ->
      expect Fixtures.Patterns.ensures_matching_a_variant_constant []);
  Harness.test "a constant whose value calls a function covers only itself" (fun () ->
      expect Fixtures.Patterns.unevaluated_constant_arm []);
  Harness.test "a constant computed by a shift covers its value" (fun () ->
      expect Fixtures.Patterns.shifted_constant_arm [ "patterns.unreachable_arm" ]);
  Harness.test "a range with Character constant ends covers their values" (fun () ->
      expect Fixtures.Patterns.range_between_character_constants [ "patterns.unreachable_arm" ]);
  Harness.test "ranges that share an end computed by a call are distinct" (fun () ->
      expect Fixtures.Patterns.ranges_from_an_unevaluated_constant [])

let () =
  let list_codes text =
    Support.list_codes
      (check (Support.setup [ ("app.main", text) ]) (Support.parse_file "app.main"))
  in
  Harness.test "a record constant covers the record it is" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.record_constant_and_record_arms
        "patterns.unreachable_arm"
        ~fixed:("(x: 0, y: false) => false\n    _ => false", "_ => false"));
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
                fn built(name: own String) -> Entry {\n\
               \  Entry(name: " ^ argument ^ ")\n}\n")
          with
          | [] -> ()
          | actual -> Harness.fail "found [%s]" (String.concat "; " actual))
        [ "own name"; "\"${name}\"" ]);
  Harness.test "a pattern that names a constant whose value fails to check reports only its error"
    (fun () ->
      match list_codes Fixtures.Patterns.arm_naming_a_constant_with_an_ill_typed_value with
      | [ code ] when not (String.starts_with ~prefix:"patterns." code) -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "a sub-pattern that failed to type makes no arm unreachable" (fun () ->
      match list_codes Fixtures.Patterns.arm_with_a_misspelled_variant with
      | actual when List.exists (fun code -> String.starts_with ~prefix:"patterns." code) actual ->
          Harness.fail "found [%s]" (String.concat "; " actual)
      | _ -> ())

let () =
  Harness.test "an alternative that an earlier arm covers is unreachable, even the first" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.alternative_an_earlier_arm_covers
        "patterns.unreachable_alternative" ~fixed:("Red | Green", "Green"));
  Harness.test "a nested alternative that the one before covers is unreachable" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.repeated_nested_alternative
        "patterns.unreachable_alternative" ~fixed:("Red | Red", "Red"))

let () =
  Harness.test "character literals and ranges cover their values" (fun () ->
      expect_one_diagnostic Fixtures.Patterns.character_range_and_literal_arms
        "patterns.unreachable_arm"
        ~fixed:("Character\"m\" => 2\n    _ => 3", "_ => 3"))

let mutually_recursive_types count =
  let name index = Printf.sprintf "Node%d" index in
  let declare index =
    let fields =
      List.filter_map
        (fun other ->
          if other = index then None
          else Some (Printf.sprintf "child%d: List[%s]" other (name other)))
        (List.init count Fun.id)
    in
    Printf.sprintf "type %s(%s)\n" (name index) (String.concat ", " fields)
  in
  String.concat "" (List.init count declare)
  ^ "fn count(node: Node0) -> UInt64 {\n\
    \  match node {\n\
    \    (child1, ..) => child1.length()\n\
    \  }\n\
     }\n"

let () =
  Harness.test "a match over many mutually recursive types visits each type once" (fun () ->
      expect_fine (mutually_recursive_types 12))
